#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0
"""generate_rust_analyzer - Generates the `rust-project.json` file for `rust-analyzer`.
"""

import argparse
import json
import logging
import os
import pathlib
import subprocess
import sys
from typing import Dict, Iterable, List, Literal, Optional, TypedDict


def args_crates_cfgs(cfgs: List[str]) -> dict[str, List[str]]:
    crates_cfgs = {}
    for cfg in cfgs:
        crate, vals = cfg.split("=", 1)
        crates_cfgs[crate] = vals.split()

    return crates_cfgs


class Dependency(TypedDict):
    crate: int
    name: str


class Source(TypedDict):
    include_dirs: List[str]
    exclude_dirs: List[str]


class Crate(TypedDict):
    display_name: str
    root_module: str
    is_workspace_member: bool
    deps: List[Dependency]
    cfg: List[str]
    edition: str
    env: Dict[str, str]


# `NotRequired` fields on `Crate` would be better but `NotRequired` was added in 3.11.
class ProcMacroCrate(Crate):
    is_proc_macro: Literal[True]
    proc_macro_dylib_path: Optional[str]  # `pathlib.Path` is not JSON serializable.


# `NotRequired` fields on `Crate` would be better but `NotRequired` was added in 3.11.
class CrateWithGenerated(Crate):
    source: Optional[Source]


def generate_crates(
    srctree: pathlib.Path,
    objtree: pathlib.Path,
    sysroot_src: pathlib.Path,
    external_src: pathlib.Path,
    cfgs: List[str],
    sysroot_edition: str,
) -> List[Crate]:
    # Generate the configuration list.
    generated_cfg = []
    with open(objtree / "include" / "generated" / "rustc_cfg") as fd:
        for line in fd:
            line = line.replace("--cfg=", "")
            line = line.replace("\n", "")
            generated_cfg.append(line)

    # Now fill the crates list.
    crates: List[Crate] = []
    crates_cfgs = args_crates_cfgs(cfgs)

    def build_crate(
        display_name: str,
        root_module: pathlib.Path,
        *,
        deps: List[Dependency],
        cfg: List[str],
        is_host: bool,
        is_workspace_member: bool,
        edition: Optional[str],
    ) -> Crate:
        if edition is None:
            edition = "2021"
        return {
            "display_name": display_name,
            "root_module": str(root_module),
            "is_workspace_member": is_workspace_member,
            "deps": deps,
            "cfg": cfg + ([] if is_host else crates_cfgs.get(display_name, [])),
            "edition": edition,
            "env": {
                "RUST_MODFILE": "This is only for rust-analyzer"
            },
        }

    def register_crate(crate: Crate) -> Dependency:
        index = len(crates)
        crates.append(crate)
        return {"crate": index, "name": crate["display_name"]}

    def append_crate(
        display_name: str,
        root_module: pathlib.Path,
        *,
        deps: List[Dependency],
        cfg: List[str] = [],
        edition: Optional[str] = None,
    ) -> Dependency:
        return register_crate(
            build_crate(
                display_name,
                root_module,
                deps=deps,
                cfg=cfg,
                is_workspace_member=True,
                is_host=False,
                edition=edition,
            )
        )

    def append_proc_macro_crate(
        display_name: str,
        root_module: pathlib.Path,
        *,
        deps: List[Dependency],
        cfg: List[str] = [],
        edition: Optional[str] = None,
    ) -> Dependency:
        crate = build_crate(
            display_name,
            root_module,
            deps=deps,
            cfg=cfg,
            is_host=False,
            is_workspace_member=True,
            edition=edition,
        )
        proc_macro_dylib_name = subprocess.check_output(
            [os.environ["RUSTC"], "--print", "file-names", "--crate-name", display_name, "--crate-type", "proc-macro", "-"],
            stdin=subprocess.DEVNULL,
        ).decode("utf-8").strip()
        proc_macro_crate: ProcMacroCrate = {
            **crate,
            "is_proc_macro": True,
            "proc_macro_dylib_path": str(objtree / "rust" / proc_macro_dylib_name),
        }
        return register_crate(proc_macro_crate)

    def append_sysroot_crate(
        display_name: str,
        *,
        deps: List[Dependency],
        cfg: List[str] = [],
        is_host: bool,
    ) -> Dependency:
        return register_crate(
            build_crate(
                display_name,
                sysroot_src / display_name / "src" / "lib.rs",
                deps=deps,
                cfg=cfg,
                is_host=is_host,
                is_workspace_member=False,
                edition=sysroot_edition,
            )
        )

    core = append_sysroot_crate("core", deps=[], is_host=False)

    # NB: sysroot crates reexport items from one another so setting up our transitive dependencies
    # here is important for ensuring that rust-analyzer can resolve symbols. The sources of truth
    # for this dependency graph are `(sysroot_src / crate / "Cargo.toml" for crate in crates)`.
    host_core = append_sysroot_crate("core", deps=[], is_host=True)
    host_alloc = append_sysroot_crate("alloc", deps=[host_core], is_host=True)
    host_std = append_sysroot_crate("std", deps=[host_alloc, host_core], is_host=True)
    host_proc_macro = append_sysroot_crate("proc_macro", deps=[host_core, host_std], is_host=True)

    compiler_builtins = append_crate(
        "compiler_builtins",
        srctree / "rust" / "compiler_builtins.rs",
        deps=[core],
    )

    proc_macro2 = append_crate(
        "proc_macro2",
        srctree / "rust" / "proc-macro2" / "lib.rs",
        deps=[host_core, host_alloc, host_std, host_proc_macro],
    )

    quote = append_crate(
        "quote",
        srctree / "rust" / "quote" / "lib.rs",
        deps=[host_alloc, host_proc_macro, proc_macro2],
        edition="2018",
    )

    syn = append_crate(
        "syn",
        srctree / "rust" / "syn" / "lib.rs",
        deps=[host_proc_macro, proc_macro2, quote],
    )

    macros = append_proc_macro_crate(
        "macros",
        srctree / "rust" / "macros" / "lib.rs",
        deps=[host_std, host_proc_macro, proc_macro2, quote, syn],
    )

    build_error = append_crate(
        "build_error",
        srctree / "rust" / "build_error.rs",
        deps=[core, compiler_builtins],
    )

    pin_init_internal = append_proc_macro_crate(
        "pin_init_internal",
        srctree / "rust" / "pin-init" / "internal" / "src" / "lib.rs",
        deps=[host_std, host_proc_macro],
        cfg=["kernel"],
    )

    pin_init = append_crate(
        "pin_init",
        srctree / "rust" / "pin-init" / "src" / "lib.rs",
        deps=[core, compiler_builtins, pin_init_internal, macros],
        cfg=["kernel"],
    )

    ffi = append_crate(
        "ffi",
        srctree / "rust" / "ffi.rs",
        deps=[core, compiler_builtins],
    )

    def append_crate_with_generated(
        display_name: str,
        *,
        deps: List[Dependency],
        edition: Optional[str] = None,
    ) -> Dependency:
        crate = build_crate(
            display_name,
            srctree / "rust" / display_name / "lib.rs",
            deps=deps,
            cfg=generated_cfg,
            is_host=False,
            is_workspace_member=True,
            edition=edition,
        )
        crate["env"]["OBJTREE"] = str(objtree.resolve(True))
        crate_with_generated: CrateWithGenerated = {
            **crate,
            "source": {
                "include_dirs": [
                    str(srctree / "rust" / display_name),
                    str(objtree / "rust"),
                ],
                "exclude_dirs": [],
            },
        }
        return register_crate(crate_with_generated)

    bindings = append_crate_with_generated("bindings", deps=[core, ffi, pin_init])
    uapi = append_crate_with_generated("uapi", deps=[core, ffi, pin_init])
    kernel = append_crate_with_generated(
        "kernel",
        deps=[
            core,
            macros,
            build_error,
            pin_init,
            ffi,
            bindings,
            uapi,
        ],
    )

    scripts = srctree / "scripts"
    makefile = (scripts / "Makefile").read_text()
    for path in scripts.glob("*.rs"):
        name = path.stem
        if f"{name}-rust" not in makefile:
            continue
        _script = append_crate(
            name,
            path,
            deps=[host_std],
            cfg=[],
        )

    def is_root_crate(build_file: pathlib.Path, target: str) -> bool:
        try:
            with open(build_file) as f:
                return f"{target}.o" in f.read()
        except FileNotFoundError:
            return False

    # Then, the rest outside of `rust/`.
    #
    # We explicitly mention the top-level folders we want to cover.
    extra_dirs: Iterable[pathlib.Path] = (srctree / dir for dir in ("samples", "drivers"))
    if external_src is not None:
        extra_dirs = [external_src]
    for folder in extra_dirs:
        for path in folder.rglob("*.rs"):
            logging.info("Checking %s", path)
            name = path.stem

            # Skip those that are not crate roots.
            if not is_root_crate(path.parent / "Makefile", name) and \
               not is_root_crate(path.parent / "Kbuild", name):
                continue

            logging.info("Adding %s", name)
            append_crate(
                name,
                path,
                deps=[core, kernel],
                cfg=generated_cfg,
            )

    return crates


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verbose", "-v", action="store_true")
    parser.add_argument("--cfgs", action="append", default=[])
    parser.add_argument("sysroot_edition")
    parser.add_argument("srctree", type=pathlib.Path)
    parser.add_argument("objtree", type=pathlib.Path)
    parser.add_argument("sysroot", type=pathlib.Path)
    parser.add_argument("sysroot_src", type=pathlib.Path)
    parser.add_argument("exttree", type=pathlib.Path, nargs="?")

    class Args(argparse.Namespace):
        verbose: bool
        cfgs: List[str]
        srctree: pathlib.Path
        objtree: pathlib.Path
        sysroot: pathlib.Path
        sysroot_src: pathlib.Path
        exttree: pathlib.Path
        sysroot_edition: str

    args = parser.parse_args(namespace=Args())

    logging.basicConfig(
        format="[%(asctime)s] [%(levelname)s] %(message)s",
        level=logging.INFO if args.verbose else logging.WARNING,
    )

    # Making sure that the `sysroot` and `sysroot_src` belong to the same toolchain.
    assert args.sysroot in args.sysroot_src.parents

    rust_project = {
        "crates": generate_crates(args.srctree, args.objtree, args.sysroot_src, args.exttree, args.cfgs, args.sysroot_edition),
        "sysroot": str(args.sysroot),
    }

    json.dump(rust_project, sys.stdout, sort_keys=True, indent=4)


if __name__ == "__main__":
    main()
