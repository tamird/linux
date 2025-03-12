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


class ProcMacroCrate(Crate):
    is_proc_macro: Literal[True]
    proc_macro_dylib_path: str  # `pathlib.Path` is not JSON serializable.


class CrateWithGenerated(Crate):
    source: Source


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

    # Now fill the crates list -- dependencies need to come first.
    #
    # Avoid O(n^2) iterations by keeping a map of indexes.
    crates: List[Crate] = []
    crates_indexes: Dict[str, int] = {}
    crates_cfgs = args_crates_cfgs(cfgs)

    def build_crate(
        display_name: str,
        root_module: pathlib.Path,
        *,
        deps: List[str],
        cfg: Optional[List[str]],
        is_workspace_member: Optional[bool],
        edition: Optional[str],
    ) -> Crate:
        if cfg is None:
            cfg = crates_cfgs.get(display_name, [])
        if is_workspace_member is None:
            is_workspace_member = True
        if edition is None:
            edition = "2021"
        return {
            "display_name": display_name,
            "root_module": str(root_module),
            "is_workspace_member": is_workspace_member,
            "deps": [{"crate": crates_indexes[dep], "name": dep} for dep in deps],
            "cfg": cfg,
            "edition": edition,
            "env": {
                "RUST_MODFILE": "This is only for rust-analyzer",
            },
        }

    def append_proc_macro_crate(
        display_name: str,
        root_module: pathlib.Path,
        *,
        deps: List[str],
        cfg: Optional[List[str]] = None,
        is_workspace_member: Optional[bool] = None,
        edition: Optional[str] = None,
    ) -> None:
        crate = build_crate(
            display_name,
            root_module,
            deps=deps,
            cfg=cfg,
            is_workspace_member=is_workspace_member,
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
        register_crate(proc_macro_crate)

    def register_crate(crate: Crate) -> None:
        crates_indexes[crate["display_name"]] = len(crates)
        crates.append(crate)

    def append_crate(
        display_name: str,
        root_module: pathlib.Path,
        *,
        deps: List[str],
        cfg: Optional[List[str]] = None,
        is_workspace_member: Optional[bool] = None,
        edition: Optional[str] = None,
    ) -> None:
        register_crate(
            build_crate(
                display_name,
                root_module,
                deps=deps,
                cfg=cfg,
                is_workspace_member=is_workspace_member,
                edition=edition,
            )
        )

    def append_sysroot_crate(
        display_name: str,
        *,
        deps: List[str],
        cfg: Optional[List[str]] = None,
    ) -> None:
        append_crate(
            display_name,
            sysroot_src / display_name / "src" / "lib.rs",
            deps=deps,
            cfg=cfg,
            is_workspace_member=False,
            edition=sysroot_edition,
        )

    # NB: sysroot crates reexport items from one another so setting up our transitive dependencies
    # here is important for ensuring that rust-analyzer can resolve symbols. The sources of truth
    # for this dependency graph are `(sysroot_src / crate / "Cargo.toml" for crate in crates)`.
    append_sysroot_crate("core", deps=[])
    append_sysroot_crate("alloc", deps=["core"])
    append_sysroot_crate("std", deps=["alloc", "core"])
    append_sysroot_crate("proc_macro", deps=["core", "std"])

    append_crate(
        "compiler_builtins",
        srctree / "rust" / "compiler_builtins.rs",
        deps=["core"],
    )

    append_crate(
        "proc_macro2",
        srctree / "rust" / "proc-macro2" / "lib.rs",
        deps=["core", "alloc", "std", "proc_macro"],
    )

    append_crate(
        "quote",
        srctree / "rust" / "quote" / "lib.rs",
        deps=["alloc", "proc_macro", "proc_macro2"],
        edition="2018",
    )

    append_crate(
        "syn",
        srctree / "rust" / "syn" / "lib.rs",
        deps=["proc_macro", "proc_macro2", "quote"],
    )

    append_proc_macro_crate(
        "macros",
        srctree / "rust" / "macros" / "lib.rs",
        deps=["std", "proc_macro", "proc_macro2", "quote", "syn"],
    )

    append_crate(
        "build_error",
        srctree / "rust" / "build_error.rs",
        deps=["core", "compiler_builtins"],
    )

    append_proc_macro_crate(
        "pin_init_internal",
        srctree / "rust" / "pin-init" / "internal" / "src" / "lib.rs",
        deps=["std", "proc_macro"],
    )

    append_crate(
        "pin_init",
        srctree / "rust" / "pin-init" / "src" / "lib.rs",
        deps=["core", "compiler_builtins", "pin_init_internal", "macros"],
    )

    append_crate(
        "ffi",
        srctree / "rust" / "ffi.rs",
        deps=["core", "compiler_builtins"],
    )

    def append_crate_with_generated(
        display_name: str,
        *,
        deps: List[str],
        is_workspace_member: Optional[bool] = None,
        edition: Optional[str] = None,
    ) -> None:
        crate = build_crate(
            display_name,
            srctree / "rust" / display_name / "lib.rs",
            deps=deps,
            cfg=generated_cfg,
            is_workspace_member=is_workspace_member,
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
        register_crate(crate_with_generated)

    append_crate_with_generated("bindings", deps=["core", "ffi", "pin_init"])
    append_crate_with_generated("uapi", deps=["core", "ffi", "pin_init"])
    append_crate_with_generated(
        "kernel",
        deps=[
            "core",
            "macros",
            "build_error",
            "pin_init",
            "ffi",
            "bindings",
            "uapi",
        ],
    )

    def is_root_crate(build_file: pathlib.Path, target: str) -> bool:
        try:
            return f"{target}.o" in open(build_file).read()
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
            name = path.name.replace(".rs", "")

            # Skip those that are not crate roots.
            if not is_root_crate(path.parent / "Makefile", name) and \
               not is_root_crate(path.parent / "Kbuild", name):
                continue

            logging.info("Adding %s", name)
            append_crate(
                name,
                path,
                deps=["core", "kernel"],
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
