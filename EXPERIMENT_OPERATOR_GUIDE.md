# Experiment run commands

`<B>` book · `<NN>` 2-digit prop · `<N>` prop no leading zero · `<M>` model · `<cost>` from `/cost`.
`eval.sh` prints `verdict=PASS|FAIL:<stage>  compile_sec=…  cost_usd=…  model=…`.

## Reset (do before a run — memory off + blank both worktrees)

Nuke memory (shared by all worktrees — removes every pointer/note):
```
rm -rf ~/.claude/projects/-h-56-taddmao-code-autoform-DNA/memory
```

Blank each worktree to its PINNED map-stage commit (`3d8e371` ablated / `be22807` full — NOT HEAD, which drifts as you commit; each restores every prop's map Main.lean + data; `git clean` removes only a prior run's untracked step files — tracked data is never touched):
```
cd ~/code/autoform/methodology_compare_worktrees/ablated
git checkout 3d8e371 -- LeanEuclidPlus/Book1 LeanEuclidPlus/Book2 LeanEuclidPlus/Book3
git clean -fd LeanEuclidPlus/Book1 LeanEuclidPlus/Book2 LeanEuclidPlus/Book3

cd ~/code/autoform/methodology_compare_worktrees/full
git checkout be22807 -- LeanEuclidPlus/Book1 LeanEuclidPlus/Book2 LeanEuclidPlus/Book3
git clean -fd LeanEuclidPlus/Book1 LeanEuclidPlus/Book2 LeanEuclidPlus/Book3
```

## Ablated

```
cd ~/code/autoform/methodology_compare_worktrees/ablated
git show 3d8e371:LeanEuclidPlus/Book<B>/Prop<NN>/Main.lean > LeanEuclidPlus/Book<B>/Prop<NN>/Main.lean
find LeanEuclidPlus/Book<B>/Prop<NN> -type f ! -name Main.lean -delete
claude --model <M>
# paste prompt · wait for cert · /cost
bash eval.sh <B> <NN> <cost> <M>
```

Prompt:
```
Prove LeanEuclidPlus/Book<B>/Prop<NN>/Main.lean — fill every ':= by sorry' so it builds with ZERO sorry. Do NOT change the theorem statement, the '(stepN : …)' claim types, or the '-- @assumption (…)' lines. Any step that has '-- @assumption' lines must be so that the corresponding euclid_sentence function after the := sorry is a function with the type of this assumption passed in to it. Also anything euclid cites, must be cited as well in Lean. Note that the venv is at ~/.venvs/leaneuclid/bin/activate for z3 and cvc5. DO NOT LOOK AT ANYTHING OUTSIDE THIS FOLDER. IF YOU DO, YOUR ATTEMPT IS AUTO-FAILED.
```
/goal this `/goal The proof assigned is faithful, compiles with no sorry, and is ready for review.`

## Full

```
cd ~/code/autoform/methodology_compare_worktrees/full
git show be22807:LeanEuclidPlus/Book<B>/Prop<NN>/Main.lean > LeanEuclidPlus/Book<B>/Prop<NN>/Main.lean
find LeanEuclidPlus/Book<B>/Prop<NN> -type f ! -name Main.lean -delete
claude --model <M>
# paste prompt · wait for cert · /cost
bash eval.sh <B> <NN> <cost> <M>
```

Prompt:
```
Prove LeanEuclidPlus/Book<B>/Prop<NN>/Main.lean end to end using /faithful-prove skill. As usual make sure --all passes, and please also wire it at the end. DO NOT LOOK AT ANYTHING OUTSIDE THIS FOLDER. IF YOU DO, YOUR ATTEMPT IS AUTO-FAILED.
```
/goal this `/goal The proof assigned is faithful (--all passed), compiles with no sorry (meaning wired ran after --all passed), and is ready for review.`
