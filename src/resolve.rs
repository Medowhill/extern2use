use std::{collections::BTreeMap, path::Path};

use etrace::some_or;
use rustc_hir::{
    def::Res, def_id::DefId, intravisit, intravisit::Visitor, FnDecl, FnRetTy, ForeignItemKind,
    HirId, ItemKind, QPath, TyKind, VariantData,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::{source_map::SourceMap, Span};

use crate::compile_util;

const UNNAMED: &str = "C2RustUnnamed";

pub fn check<P: AsRef<Path>>(path: P) {
    let input = compile_util::path_to_input(path);
    let (config, arc) = compile_util::make_counting_config(input);
    compile_util::run_compiler(config, |_, tcx| {
        let _ = tcx.analysis(());
    })
    .unwrap();
    let errors = *arc.lock().unwrap();
    assert_eq!(errors, 0);
}

pub fn rename_unnamed<P: AsRef<Path>>(path: P) {
    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let suggestions = compile_util::run_compiler(config, |source_map, tcx| {
        let hir = tcx.hir();

        let mut next_idx = 0;
        let mut types: BTreeMap<_, Vec<_>> = BTreeMap::new();
        for id in hir.items() {
            let item = hir.item(id);
            let name = item.ident.name.to_ident_string();
            let idx = some_or!(name.strip_prefix(UNNAMED), continue);
            if let Some(i) = idx.strip_prefix('_') {
                let i: usize = i.parse().unwrap();
                next_idx = next_idx.max(i + 1);
            }
            match &item.kind {
                ItemKind::Struct(v, _) | ItemKind::Union(v, _) => {
                    let is_struct = matches!(item.kind, ItemKind::Struct(_, _));
                    let fs = if let VariantData::Struct(fs, _) = v {
                        fs
                    } else {
                        unreachable!("{:?}", item)
                    };
                    let fs: Vec<_> = fs
                        .iter()
                        .map(|f| source_map.span_to_snippet(f.span).unwrap())
                        .collect();
                    types.entry((is_struct, fs)).or_default().push(item);
                }
                ItemKind::Enum(_, _) => unreachable!("{:?}", item),
                _ => {}
            }
        }

        let mut visitor = PathVisitor::new(tcx);
        tcx.hir().visit_all_item_likes_in_crate(&mut visitor);

        let mut suggestions: BTreeMap<_, Vec<_>> = BTreeMap::new();
        for items in types.into_values() {
            let new_name = format!("{}_{}", UNNAMED, next_idx);
            next_idx += 1;

            let mut per_file: BTreeMap<_, Vec<_>> = BTreeMap::new();
            for item in items {
                let file = compile_util::span_to_path(item.span, source_map).unwrap();
                per_file.entry(file).or_default().push(item);
            }

            for (file, items) in per_file {
                let v = suggestions.entry(file).or_default();

                let mut first = true;
                for item in items {
                    let new_name2 = if first {
                        first = false;
                        new_name.clone()
                    } else {
                        let new_name = format!("{}_{}", UNNAMED, next_idx);
                        next_idx += 1;
                        new_name
                    };
                    let snippet = compile_util::span_to_snippet(item.ident.span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, &new_name2);
                    v.push(suggestion);

                    let name = item.ident.name.to_ident_string();
                    let def_id = item.item_id().owner_id.def_id.to_def_id();
                    let spans = some_or!(visitor.paths.get(&def_id), continue);
                    for span in spans {
                        if source_map.span_to_snippet(*span).unwrap() != name {
                            continue;
                        }
                        let snippet = compile_util::span_to_snippet(*span, source_map);
                        let suggestion = compile_util::make_suggestion(snippet, &new_name);
                        v.push(suggestion);
                    }
                }
            }
        }

        suggestions
    })
    .unwrap();
    compile_util::apply_suggestions(&suggestions);
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct FunSig {
    name: String,
    params: Vec<String>,
    ret: String,
}

impl FunSig {
    fn new(name: String, decl: &FnDecl<'_>, source_map: &SourceMap) -> Self {
        let params = decl
            .inputs
            .iter()
            .map(|ty| source_map.span_to_snippet(ty.span).unwrap())
            .collect();
        let ret = if let FnRetTy::Return(ty) = &decl.output {
            source_map.span_to_snippet(ty.span).unwrap()
        } else {
            "()".to_string()
        };
        Self { name, params, ret }
    }
}

pub fn deduplicate<P: AsRef<Path>>(path: P) {
    let mut dir = path.as_ref().to_path_buf();
    dir.pop();

    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let suggestions = compile_util::run_compiler(config, |source_map, tcx| {
        let hir = tcx.hir();

        let mut functions = BTreeMap::new();
        let mut ffunctions: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut ftypes: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut uspans = BTreeMap::new();
        let mut structs: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut impls = BTreeMap::new();

        for id in hir.items() {
            let item = hir.item(id);
            let name = item.ident.name.to_ident_string();
            let file = some_or!(compile_util::span_to_path(item.span, source_map), continue);
            match &item.kind {
                ItemKind::Fn(sig, _, _) => {
                    if tcx.visibility(item.owner_id).is_public() {
                        let rp = mk_rust_path(&dir, &file, &name);
                        let sig = FunSig::new(name, sig.decl, source_map);
                        functions.insert(sig, rp);
                    }
                }
                ItemKind::ForeignMod { items, .. } => {
                    let fv = ffunctions.entry(file.clone()).or_default();
                    let ft = ftypes.entry(file).or_default();
                    for item in items.iter() {
                        let item = hir.foreign_item(item.id);
                        let name = item.ident.name.to_ident_string();
                        let span = source_map.span_extend_to_line(item.span);
                        match &item.kind {
                            ForeignItemKind::Fn(decl, _, _) => {
                                let sig = FunSig::new(name, decl, source_map);
                                fv.push((sig, span));
                            }
                            ForeignItemKind::Type => ft.push((name, span)),
                            _ => {}
                        }
                    }
                }
                ItemKind::Struct(_, _) | ItemKind::Union(_, _) => {
                    structs.entry(name).or_default().push((file, item.span));
                }
                ItemKind::Enum(_, _) => unreachable!("{:?}", item),
                ItemKind::Impl(i) => {
                    if let TyKind::Path(QPath::Resolved(_, path)) = &i.self_ty.kind {
                        let seg = path.segments.last().unwrap();
                        let name = seg.ident.name.to_ident_string().to_string();
                        let span = source_map.span_extend_to_line(item.span);
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

        for (p, fs) in ffunctions {
            let mut v = vec![];
            let uspan = uspans.get(&p).unwrap();

            for (sig, span) in fs {
                let rp = some_or!(functions.get(&sig), continue);

                let stmt = format!("\nuse {};", rp);
                let snippet = compile_util::span_to_snippet(*uspan, source_map);
                let suggestion = compile_util::make_suggestion(snippet, &stmt);
                v.push(suggestion);

                let snippet = compile_util::span_to_snippet(span, source_map);
                let suggestion = compile_util::make_suggestion(snippet, "");
                v.push(suggestion);
            }

            if !v.is_empty() {
                suggestions.insert(p.clone(), v);
            }
        }

        let mut struct_map = BTreeMap::new();

        for (name, mut ts) in structs {
            let file = ts.pop().unwrap().0;
            let rp = mk_rust_path(&dir, &file, &name);
            struct_map.insert(name.clone(), rp.clone());

            for (file, span) in ts {
                let v = suggestions.entry(file.clone()).or_default();

                let uspan = uspans.get(&file).unwrap();
                let stmt = format!("\nuse {};", rp);
                let snippet = compile_util::span_to_snippet(*uspan, source_map);
                let suggestion = compile_util::make_suggestion(snippet, &stmt);
                v.push(suggestion);

                let impl_span = impls.get(&(file.clone(), name.clone())).unwrap();
                let span = span.with_lo(impl_span.lo());
                let snippet = compile_util::span_to_snippet(span, source_map);
                let suggestion = compile_util::make_suggestion(snippet, "");
                v.push(suggestion);
            }
        }

        let mut foreign_types: BTreeMap<_, Vec<_>> = BTreeMap::new();
        for (file, ts) in ftypes {
            let v = suggestions.entry(file.clone()).or_default();
            let uspan = uspans.get(&file).unwrap();
            for (ty, span) in ts {
                if let Some(rp) = struct_map.get(&ty) {
                    let stmt = format!("\nuse {};", rp);
                    let snippet = compile_util::span_to_snippet(*uspan, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, &stmt);
                    v.push(suggestion);

                    let snippet = compile_util::span_to_snippet(span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, "");
                    v.push(suggestion);
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
            let rp = mk_rust_path(&dir, file, ty);
            for (file, span) in fss {
                let v = suggestions.entry(file.clone()).or_default();
                let uspan = uspans.get(&file).unwrap();

                let stmt = format!("\nuse {};", rp);
                let snippet = compile_util::span_to_snippet(*uspan, source_map);
                let suggestion = compile_util::make_suggestion(snippet, &stmt);
                v.push(suggestion);

                let snippet = compile_util::span_to_snippet(span, source_map);
                let suggestion = compile_util::make_suggestion(snippet, "");
                v.push(suggestion);
            }
        }

        suggestions
    })
    .unwrap();
    compile_util::apply_suggestions(&suggestions);
}

fn mk_rust_path<P: AsRef<Path>, Q: AsRef<Path>, S: AsRef<str>>(dir: P, path: Q, name: S) -> String {
    let mut path = path.as_ref().strip_prefix(dir).unwrap().to_path_buf();
    path.set_extension("");
    std::iter::once("crate")
        .chain(path.components().map(|c| c.as_os_str().to_str().unwrap()))
        .chain(std::iter::once(name.as_ref()))
        .intersperse("::")
        .collect()
}
