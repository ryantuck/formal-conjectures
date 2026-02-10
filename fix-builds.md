# Fix Builds

Read `ai-formalization-instructions-erdos.md` for details on workflow for implementing Erdos conjectures in lean.

## Build Logs

the `build-logs/` dir is to be treated as the canonical source of truth for whether builds are working or not.

## Failed builds

The `Makefile` contains the build target `failed-builds.txt` to keep track of erdos problems for which the build is failing.

Force rebuilds of this using make's `-B` flag:

```
make failing-builds.txt -B
```

## Building

Use the following command to build erdos problem NUMBER and successfully log.

```
lake build FormalConjectures/ErdosProblems/NUMBER.lean | tee build-logs/NUMBER.txt
```

