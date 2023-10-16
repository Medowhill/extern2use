use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{File, OpenOptions},
    io::Write as _,
    path::{Path, PathBuf},
};

use etrace::some_or;
use lazy_static::lazy_static;
use rustc_hir::{
    def::{DefKind, Res},
    def_id::DefId,
    intravisit,
    intravisit::Visitor,
    FnDecl, FnRetTy, ForeignItemKind, HirId, ItemKind, PatKind, QPath, Ty, TyKind, VariantData,
};
use rustc_middle::{
    hir::{map::Map, nested_filter},
    ty::TyCtxt,
};
use rustc_span::{source_map::SourceMap, Span};
use rustfix::{Snippet, Suggestion};

use crate::compile_util;

const UNNAMED: &str = "C2RustUnnamed";

pub fn check(path: &Path) {
    let input = compile_util::path_to_input(path);
    let (config, arc) = compile_util::make_counting_config(input);
    compile_util::run_compiler(config, |tcx| {
        let _ = tcx.analysis(());
    })
    .unwrap();
    let errors = *arc.lock().unwrap();
    assert_eq!(errors, 0);
}

pub fn rename_unnamed(path: &Path) -> bool {
    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let suggestions =
        compile_util::run_compiler(config, |tcx| Resolver::new(tcx).rename_unnamed()).unwrap();
    compile_util::apply_suggestions(&suggestions);
    !suggestions.is_empty()
}

pub fn deduplicate_types(path: &Path) -> bool {
    let mut dir = path.to_path_buf();
    dir.pop();

    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let suggestions =
        compile_util::run_compiler(config, |tcx| Resolver::new(tcx).deduplicate_types(&dir))
            .unwrap();
    compile_util::apply_suggestions(&suggestions);
    !suggestions.is_empty()
}

pub fn deduplicate_type_aliases(path: &Path) -> bool {
    let mut dir = path.to_path_buf();
    dir.pop();

    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let suggestions = compile_util::run_compiler(config, |tcx| {
        Resolver::new(tcx).deduplicate_type_aliases(&dir)
    })
    .unwrap();
    compile_util::apply_suggestions(&suggestions);
    !suggestions.is_empty()
}

pub fn deduplicate_fns(path: &Path) -> bool {
    let mut dir = path.to_path_buf();
    dir.pop();

    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let suggestions =
        compile_util::run_compiler(config, |tcx| Resolver::new(tcx).deduplicate_fns(&dir)).unwrap();
    compile_util::apply_suggestions(&suggestions);
    !suggestions.is_empty()
}

pub fn resolve_conflicts(path: &Path) -> bool {
    let mut dir = path.to_path_buf();
    dir.pop();

    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let suggestions =
        compile_util::run_compiler(config, |tcx| Resolver::new(tcx).resolve_conflicts()).unwrap();
    compile_util::apply_suggestions(&suggestions);
    !suggestions.is_empty()
}

pub fn add_bin(path: &Path) {
    let mut dir = path.to_path_buf();
    dir.pop();

    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let rps =
        compile_util::run_compiler(config, |tcx| Resolver::new(tcx).find_mains(&dir)).unwrap();

    let mut cargo_file = OpenOptions::new()
        .append(true)
        .open(dir.join("Cargo.toml"))
        .unwrap();

    for rp in rps {
        let name = rp.replace("::", "_").replace("r#", "");
        let filename = format!("{}.rs", name);
        let path = dir.join(&filename);
        let mut file = File::create_new(path).unwrap();
        file.write_all(format!("fn main() {{ {}(); }}", rp).as_bytes())
            .unwrap();
        cargo_file
            .write_all(
                format!("\n[[bin]]\nname = \"{}\"\npath = \"{}\"", name, filename).as_bytes(),
            )
            .unwrap();
    }
}

struct Resolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    uses: BTreeMap<PathBuf, BTreeSet<String>>,
}

type Suggestions = BTreeMap<PathBuf, Vec<Suggestion>>;

impl<'tcx> Resolver<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            uses: BTreeMap::new(),
        }
    }

    fn hir(&self) -> Map<'tcx> {
        self.tcx.hir()
    }

    fn source_map(&self) -> &SourceMap {
        self.tcx.sess.source_map()
    }

    fn span_to_snippet(&self, span: Span) -> Snippet {
        compile_util::span_to_snippet(span, self.source_map())
    }

    fn span_to_path(&self, span: Span) -> Option<PathBuf> {
        compile_util::span_to_path(span, self.source_map())
    }

    fn span_to_string(&self, span: Span) -> String {
        self.source_map().span_to_snippet(span).unwrap()
    }

    fn add_use(&mut self, file: PathBuf, path: String) {
        self.uses.entry(file).or_default().insert(path);
    }

    fn rename_unnamed(&self) -> Suggestions {
        let mut next_idx = 0;
        let mut types: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut impls = BTreeMap::new();

        for id in self.hir().items() {
            let item = self.hir().item(id);
            let name = item.ident.name.to_ident_string();

            if let ItemKind::Impl(i) = &item.kind {
                if let TyKind::Path(QPath::Resolved(_, path)) = &i.self_ty.kind {
                    let file = some_or!(self.span_to_path(item.span), continue);
                    let seg = path.segments.last().unwrap();
                    let name = seg.ident.name.to_ident_string().to_string();
                    let span = self.source_map().span_extend_to_line(item.span);
                    impls.insert((file, name), span);
                }
            }

            let idx = some_or!(name.strip_prefix(UNNAMED), continue);
            if let Some(i) = idx.strip_prefix('_') {
                let i: usize = i.parse().unwrap();
                next_idx = next_idx.max(i + 1);
            }

            match &item.kind {
                ItemKind::Struct(v, _) | ItemKind::Union(v, _) => {
                    let is_struct = matches!(item.kind, ItemKind::Struct(_, _)) as usize;
                    let fs = if let VariantData::Struct(fs, _) = v {
                        fs
                    } else {
                        unreachable!("{:?}", item)
                    };
                    let fs: Vec<_> = fs.iter().map(|f| self.span_to_string(f.span)).collect();
                    types.entry((is_struct, fs)).or_default().push(item);
                }
                ItemKind::Enum(_, _) => unreachable!("{:?}", item),
                ItemKind::TyAlias(ty, _) => {
                    let fs = vec![self.span_to_string(ty.span)];
                    types.entry((2, fs)).or_default().push(item);
                }
                _ => {}
            }
        }

        let mut visitor = PathVisitor::new(self.tcx);
        self.hir().visit_all_item_likes_in_crate(&mut visitor);

        let mut suggestions: BTreeMap<_, Vec<_>> = BTreeMap::new();
        for items in types.into_values() {
            let names: BTreeSet<_> = items
                .iter()
                .map(|item| item.ident.name.to_string())
                .collect();
            if names.len() == 1 {
                continue;
            }

            let new_name = format!("{}_{}", UNNAMED, next_idx);
            next_idx += 1;

            let mut per_file: BTreeMap<_, Vec<_>> = BTreeMap::new();
            for item in items {
                let file = self.span_to_path(item.span).unwrap();
                per_file.entry(file).or_default().push(item);
            }

            for (file, items) in per_file {
                let v = suggestions.entry(file.clone()).or_default();

                let mut first = true;
                for item in items {
                    if first {
                        let snippet = self.span_to_snippet(item.ident.span);
                        let suggestion = compile_util::make_suggestion(snippet, &new_name);
                        v.push(suggestion);

                        first = false;
                    } else {
                        let name = item.ident.name.to_ident_string();
                        let span = if let Some(impl_span) = impls.get(&(file.clone(), name.clone()))
                        {
                            item.span.with_lo(impl_span.lo())
                        } else {
                            item.span
                        };
                        let snippet = self.span_to_snippet(span);
                        let suggestion = compile_util::make_suggestion(snippet, "");
                        v.push(suggestion);
                    }

                    let name = item.ident.name.to_ident_string();
                    let def_id = item.item_id().owner_id.def_id.to_def_id();
                    let spans = some_or!(visitor.paths.get(&def_id), continue);
                    for span in spans {
                        if self.span_to_string(*span) != name {
                            continue;
                        }
                        let snippet = self.span_to_snippet(*span);
                        let suggestion = compile_util::make_suggestion(snippet, &new_name);
                        v.push(suggestion);
                    }
                }
            }
        }

        suggestions.retain(|_, v| !v.is_empty());
        suggestions
    }

    fn deduplicate_types(&self, dir: &Path) -> Suggestions {
        let mut ftypes: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut uspans = BTreeMap::new();
        let mut structs: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut impls = BTreeMap::new();

        for id in self.hir().items() {
            let item = self.hir().item(id);
            let name = item.ident.name.to_ident_string();
            let file = some_or!(self.span_to_path(item.span), continue);
            match &item.kind {
                ItemKind::ForeignMod { items, .. } => {
                    let ft = ftypes.entry(file).or_default();
                    for item in items.iter() {
                        let item = self.hir().foreign_item(item.id);
                        let name = item.ident.name.to_ident_string();
                        let span = self.source_map().span_extend_to_line(item.span);
                        if matches!(item.kind, ForeignItemKind::Type) {
                            ft.push((name, span));
                        }
                    }
                }
                ItemKind::Struct(v, _) | ItemKind::Union(v, _) => {
                    let fs = if let VariantData::Struct(fs, _) = v {
                        fs
                    } else {
                        unreachable!("{:?}", item)
                    };
                    let fs: Vec<_> = fs.iter().map(|f| self.span_to_string(f.span)).collect();
                    structs
                        .entry((name, fs))
                        .or_default()
                        .push((file, item.span));
                }
                ItemKind::Enum(_, _) => unreachable!("{:?}", item),
                ItemKind::Impl(i) => {
                    if let TyKind::Path(QPath::Resolved(_, path)) = &i.self_ty.kind {
                        let seg = path.segments.last().unwrap();
                        let name = seg.ident.name.to_ident_string().to_string();
                        let span = self.source_map().span_extend_to_line(item.span);
                        impls.insert((file, name), span);
                    }
                }
                ItemKind::Use(path, _) => {
                    let seg = path.segments.last().unwrap();
                    if seg.ident.name.to_ident_string() == "libc" {
                        uspans.insert(file, item.span.shrink_to_hi());
                    }
                }
                _ => {}
            }
        }

        let mut suggestions: BTreeMap<_, Vec<_>> = BTreeMap::new();

        let mut struct_map = BTreeMap::new();

        for ((name, _), mut ts) in structs {
            let file = ts.pop().unwrap().0;
            let rp = mk_rust_path(dir, &file, "crate", &name);
            struct_map.insert(name.clone(), rp.clone());

            for (file, span) in ts {
                let v = suggestions.entry(file.clone()).or_default();
                let uspan = uspans.get(&file).unwrap();
                let impl_span = impls.get(&(file.clone(), name.clone())).unwrap();
                let span = span.with_lo(impl_span.lo());
                self.replace_with_use(&rp, *uspan, span, &file, v);
            }
        }

        let mut foreign_types: BTreeMap<_, Vec<_>> = BTreeMap::new();
        for (file, ts) in ftypes {
            let v = suggestions.entry(file.clone()).or_default();
            let uspan = uspans.get(&file).unwrap();
            for (ty, span) in ts {
                if let Some(rp) = struct_map.get(&ty) {
                    self.replace_with_use(rp, *uspan, span, &file, v);
                } else {
                    foreign_types
                        .entry(ty)
                        .or_default()
                        .push((file.clone(), span));
                }
            }
        }

        for (ty, mut fss) in foreign_types {
            let (file, _) = fss.pop().unwrap();
            let rp = mk_rust_path(dir, &file, "crate", &ty);
            for (file, span) in fss {
                let v = suggestions.entry(file.clone()).or_default();
                let uspan = uspans.get(&file).unwrap();
                self.replace_with_use(&rp, *uspan, span, &file, v);
            }
        }

        suggestions.retain(|_, v| !v.is_empty());
        suggestions
    }

    fn deduplicate_type_aliases(&self, dir: &Path) -> Suggestions {
        let mut types: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut uspans = BTreeMap::new();

        for id in self.hir().items() {
            let item = self.hir().item(id);
            let name = item.ident.name.to_ident_string();
            let file = some_or!(self.span_to_path(item.span), continue);
            match &item.kind {
                ItemKind::TyAlias(ty, _) => {
                    if self.span_to_string(item.span) == "BitfieldStruct" {
                        continue;
                    }
                    types
                        .entry((name, self.ty_to_string(ty)))
                        .or_default()
                        .push((file, item.span));
                }
                ItemKind::Use(path, _) => {
                    let seg = path.segments.last().unwrap();
                    if seg.ident.name.to_ident_string() == "libc" {
                        uspans.insert(file, item.span.shrink_to_hi());
                    }
                }
                _ => {}
            }
        }

        let mut suggestions: BTreeMap<_, Vec<_>> = BTreeMap::new();

        for ((name, _), mut fss) in types {
            let (file, _) = fss.pop().unwrap();
            let rp = mk_rust_path(dir, &file, "crate", &name);

            for (file, span) in fss {
                let v = suggestions.entry(file.clone()).or_default();
                let uspan = uspans.get(&file).unwrap();
                self.replace_with_use(&rp, *uspan, span, &file, v);
            }
        }

        suggestions.retain(|_, v| !v.is_empty());
        suggestions
    }

    fn deduplicate_fns(&mut self, dir: &Path) -> Suggestions {
        let mut functions = BTreeMap::new();
        let mut ffunctions: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut variables = BTreeMap::new();
        let mut fvariables: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut uspans = BTreeMap::new();

        for id in self.hir().items() {
            let item = self.hir().item(id);
            let name = item.ident.name.to_ident_string();
            let file = some_or!(self.span_to_path(item.span), continue);
            match &item.kind {
                ItemKind::Fn(sig, _, _) => {
                    if self.tcx.visibility(item.owner_id).is_public() {
                        let rp = mk_rust_path(dir, &file, "crate", &name);
                        let sig = self.mk_fun_sig(name, sig.decl);
                        functions.insert(sig, rp);
                    }
                }
                ItemKind::Static(ty, _, _) => {
                    if self.tcx.visibility(item.owner_id).is_public() {
                        let rp = mk_rust_path(dir, &file, "crate", &name);
                        let ty = clear_len(&self.ty_to_string(ty));
                        variables.insert((name, ty), rp);
                    }
                }
                ItemKind::ForeignMod { items, .. } => {
                    let fv = ffunctions.entry(file.clone()).or_default();
                    let vv = fvariables.entry(file.clone()).or_default();
                    for item in items.iter() {
                        let item = self.hir().foreign_item(item.id);
                        let name = item.ident.name.to_ident_string();
                        let span = self.source_map().span_extend_to_line(item.span);
                        let hir_id = self.hir().local_def_id_to_hir_id(item.owner_id.def_id);
                        let attrs = self.hir().attrs(hir_id);
                        let min = attrs.iter().map(|a| a.span.lo()).min().unwrap_or(span.lo());
                        let span = span.with_lo(min);
                        match &item.kind {
                            ForeignItemKind::Fn(decl, _, _) => {
                                let sig = self.mk_fun_sig(name, decl);
                                fv.push((sig, span));
                            }
                            ForeignItemKind::Static(ty, _) => {
                                let ty = clear_len(&self.ty_to_string(ty));
                                vv.push(((name, ty), span));
                            }
                            _ => {}
                        }
                    }
                }
                ItemKind::Use(path, _) => {
                    let seg = path.segments.last().unwrap();
                    if seg.ident.name.to_ident_string() == "libc" {
                        uspans.insert(file.clone(), item.span.shrink_to_hi());
                    }
                    self.add_use(file, self.span_to_string(path.span));
                }
                _ => {}
            }
        }

        let mut suggestions: BTreeMap<_, Vec<_>> = BTreeMap::new();
        for (p, fs) in ffunctions {
            let v = suggestions.entry(p.clone()).or_default();
            let uspan = uspans.get(&p).unwrap();

            for (sig, span) in fs {
                let rp = some_or!(functions.get(&sig), continue);
                self.replace_with_use(rp, *uspan, span, &p, v);
            }
        }

        for (p, vs) in fvariables {
            let v = suggestions.entry(p.clone()).or_default();
            let uspan = uspans.get(&p).unwrap();

            for (ty, span) in vs {
                let rp = some_or!(variables.get(&ty), continue);
                self.replace_with_use(rp, *uspan, span, &p, v);
            }
        }

        suggestions.retain(|_, v| !v.is_empty());
        suggestions
    }

    fn resolve_conflicts(&mut self) -> Suggestions {
        let mut suggestions: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut locals: BTreeMap<_, BTreeMap<_, Vec<_>>> = BTreeMap::new();
        let mut uses: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();

        for id in self.hir().items() {
            let item = self.hir().item(id);
            let file = some_or!(self.span_to_path(item.span), continue);
            match &item.kind {
                ItemKind::Fn(_, _, body_id) => {
                    let body = self.hir().body(*body_id);
                    let mut visitor = LocalVisitor::new(self.tcx);
                    visitor.visit_body(body);
                    for (name, spans) in visitor.locals {
                        locals
                            .entry(file.clone())
                            .or_default()
                            .entry(name)
                            .or_default()
                            .extend(spans);
                    }
                }
                ItemKind::Use(path, _) => {
                    let is_static = path
                        .res
                        .iter()
                        .any(|res| matches!(res, Res::Def(DefKind::Static(_), _)));
                    if is_static {
                        let seg = path.segments.last().unwrap().ident.name.to_ident_string();
                        uses.entry(file.clone()).or_default().insert(seg);
                    }
                }
                _ => {}
            }
        }

        let empty = BTreeSet::new();
        for (file, locals) in locals {
            let uses = uses.get(&file).unwrap_or(&empty);
            let v = suggestions.entry(file).or_default();
            for (name, spans) in locals {
                if !uses.contains(&name) {
                    continue;
                }
                let new_name = format!("{}__new", name);
                for span in spans {
                    let snippet = self.span_to_snippet(span);
                    let suggestion = compile_util::make_suggestion(snippet, &new_name);
                    v.push(suggestion);
                }
            }
        }

        suggestions.retain(|_, v| !v.is_empty());
        suggestions
    }

    fn find_mains(&self, dir: &Path) -> Vec<String> {
        let mut rps = vec![];
        for id in self.hir().items() {
            let item = self.hir().item(id);
            let name = item.ident.name.to_ident_string();
            let file = some_or!(self.span_to_path(item.span), continue);
            if matches!(item.kind, ItemKind::Fn(_, _, _)) && name == "main" {
                rps.push(mk_rust_path(dir, &file, "c2rust_out", "main"));
            }
        }
        rps
    }

    fn replace_with_use(
        &self,
        rp: &str,
        uspan: Span,
        span: Span,
        file: &PathBuf,
        v: &mut Vec<Suggestion>,
    ) {
        let empty = BTreeSet::new();
        if !self.uses.get(file).unwrap_or(&empty).contains(rp) {
            let stmt = format!("\nuse {};", rp);
            let snippet = self.span_to_snippet(uspan);
            let suggestion = compile_util::make_suggestion(snippet, &stmt);
            v.push(suggestion);
        }

        let snippet = self.span_to_snippet(span);
        let suggestion = compile_util::make_suggestion(snippet, "");
        v.push(suggestion);
    }

    fn mk_fun_sig(&self, name: String, decl: &'tcx FnDecl<'tcx>) -> FunSig {
        let params = decl.inputs.iter().map(|ty| self.ty_to_string(ty)).collect();
        let ret = if let FnRetTy::Return(ty) = &decl.output {
            self.ty_to_string(ty)
        } else {
            "()".to_string()
        };
        FunSig { name, params, ret }
    }

    fn ty_to_string(&self, ty: &'tcx Ty<'tcx>) -> String {
        let mut visitor = PathVisitor::new(self.tcx);
        visitor.visit_ty(ty);
        let mut substs: Vec<_> = visitor
            .paths
            .into_iter()
            .flat_map(|(def_id, spans)| {
                let def_path = self.tcx.def_path_str(def_id);
                if def_path == "std::option::Option" {
                    vec![]
                } else {
                    spans
                        .into_iter()
                        .map(|span| (self.span_to_string(span), def_path.clone()))
                        .collect::<Vec<_>>()
                }
            })
            .collect();
        substs.sort_by_key(|(s, _)| usize::MAX - s.len());
        let mut ty_str = self.span_to_string(ty.span);
        for (old, new) in substs {
            ty_str = ty_str.replace(&old, &new);
        }
        ty_str
    }
}

struct PathVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    paths: BTreeMap<DefId, Vec<Span>>,
}

impl<'tcx> PathVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            paths: BTreeMap::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for PathVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_path(&mut self, path: &rustc_hir::Path<'tcx>, _: HirId) {
        if let Res::Def(_, def_id) = path.res {
            self.paths.entry(def_id).or_default().push(path.span);
        }
        intravisit::walk_path(self, path);
    }
}

struct LocalVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    locals: BTreeMap<String, Vec<Span>>,
}

impl<'tcx> LocalVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            locals: BTreeMap::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for LocalVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
        if let PatKind::Binding(_, _, id, _) = pat.kind {
            let name = id.name.to_ident_string();
            self.locals.entry(name).or_default().push(id.span);
        }
        intravisit::walk_pat(self, pat);
    }

    fn visit_path(&mut self, path: &rustc_hir::Path<'tcx>, _: HirId) {
        if matches!(path.res, Res::Local(_)) {
            let name = self
                .tcx
                .sess
                .source_map()
                .span_to_snippet(path.span)
                .unwrap();
            self.locals.entry(name).or_default().push(path.span);
        }
        intravisit::walk_path(self, path);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct FunSig {
    name: String,
    params: Vec<String>,
    ret: String,
}

fn mk_rust_path(dir: &Path, path: &Path, root: &str, name: &str) -> String {
    let mut path = path.strip_prefix(dir).unwrap().to_path_buf();
    path.set_extension("");
    let mut res = root.to_string();
    for c in path.components() {
        res += "::";
        let seg = c.as_os_str().to_str().unwrap();
        if KEYWORDS.contains(seg) {
            res += "r#";
        }
        res += seg;
    }
    res += "::";
    res += name;
    res
}

fn clear_len(s: &str) -> String {
    let re = regex::Regex::new(r"; \d*]").unwrap();
    re.replace_all(s, "; 0]").to_string()
}

lazy_static! {
    static ref KEYWORDS: BTreeSet<&'static str> = [
        "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false", "fn",
        "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref",
        "return", "self", "Self", "static", "struct", "super", "trait", "true", "type", "unsafe",
        "use", "where", "while", "async", "await", "dyn", "abstract", "become", "box", "do",
        "final", "macro", "override", "priv", "typeof", "unsized", "virtual", "yield", "try",
    ]
    .into_iter()
    .collect();
}
