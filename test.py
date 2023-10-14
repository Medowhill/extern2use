#! /usr/bin/env python3

import os, subprocess

base_dir = os.path.expanduser("~/rs-gnu")
output_dir = os.path.expanduser("~/rs-gnu-resolved")

env = os.environ.copy()
env["RUSTFLAGS"] = "-Awarnings"

for dir_name in os.listdir(base_dir):
    dir_path = os.path.join(base_dir, dir_name)

    if not os.path.isdir(dir_path):
        continue

    command = [
        "cargo",
        "run",
        "--release",
        "--",
        "-o",
        output_dir,
        dir_path,
    ]
    subprocess.run(command, check=True)

    new_dir_path = os.path.join(output_dir, dir_name)

    for f in os.listdir(new_dir_path) :
        if not (f.startswith("c2rust_out_") and f.endswith("_main.rs")):
            continue

        name = os.path.splitext(f)[0] 

        if dir_name == "mcsim-6.2.0" and name == "c2rust_out_sim_sim_main":
            continue

        command = ["cargo", "build", "--bin", name]
        subprocess.run(command, check=True, cwd=new_dir_path, env=env)
