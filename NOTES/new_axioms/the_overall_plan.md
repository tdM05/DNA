# TLDR
We are *not* aiming for the "best" set of axioms. Rather, we propose a benchmark for evaluating axiom creation. This could be human or agentic-framework created axioms. Then alongside this, we propose our own set of axioms that work and prove all of the Elements.

There are **two essential contributions.**
1. We are the first to formalize Euclid's Elements, which has not been done for two thousand years. This book is arguably the most influencial textbook of all time and shaped the very foundations of mathematics so being the first to formalized is an achievement.
2. We are (maybe) the first to open the door to the field of agentic-axiom creation, which is about how to create a "good" set of axioms (can call *axiom learning*) and we contribute a benchmark for evaluating such frameworks. This may be extrememly important in the near future. So far AI formalize math, built on top of axioms, but AI may develop their own mathematical fields, that is their own axioms, and we need to have some way of evaluating such axioms. The developmenet of new fields is not just "for show". The development of "meta-math" like FOL, dependent type theory, etc., made Lean/SMT solvers and other proof checkers even possible in the first place.

## The Benchmark
**Input:** Set of axioms *for the allowed axioms to change*
**Output:** Outputs a natural number $n$ representing the score. For now, $n$ is just the number of total new symbols in the *new added axioms after fully expanding*. A symbol is a constant symbol, a connective (like '(', ')', \to ...). Fully expand means if ever there is a def that hides other defs, we expand this.

**Criteria:** 
1. Keeping the proof map fixed (euclid_sentence types, not the proof of that type), the new axioms are able to prove each subgoal using their own axioms. Note that certain axioms are required to exist, namely those in the proof map, so like types for example since these are required for faithfulness.
2. They prove soundness w.r.t. F^2 (or whatever appropriate model in the corresponding book) just like how we do.
3. They prove completeness w.r.t F^2 just like we do.

1. is the most important criteria 2. is nice to have and optional, while 3. is probably not going to be enforced for now.

**Worst case dummy example**
This is a thought experiment illustrating what we *want to claim as the worst performing* methodology on this benchmark. It is for every single step, we create its own axiom for it. The idea is the eval should always make this the worst case. The goal is to do better than this. Technically we can maybe do worse by having additional unused axiosm but this is just high level idea.

## RQs
### Benchmark methodology
- stuffs like why we keep the mapping stage (guarantee faithfulness so don't worry about faithfulness issues), how we decide what axioms cannot be changed, the idea fo the benchmark etc.
### What is our score compared to baseline
- our score is done manaully be a human (expert, even though I do not think I am expert here), and compared to naive baseline where every single step is formalized. I think we can have a lower bound on every step since doing it all manually is a pain and then we can say "at least x times better".

###
