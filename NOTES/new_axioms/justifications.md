# How System E does it
Let $\mathcal{F}$ be the set of all euclidean fields (ordered field and non-negative elements are a square) 

They claim FxF is an appropriate model for euclidean geometry, and prove that 
1. for any formula $\alpha$, whenever $\Delta \vdash \alpha$, we have for any $F \in \mathcal{F}, F^2 \vDash \alpha$. *Can think of as saying* whenever $\Delta \vdash \alpha$, $\Delta \vDash \alpha$ over $F^2$ where $F \in \mathcal{F}$
2. for any formula $\alpha$, if (for every $F\in \mathcal{F}$, $F^2 \vDash \alpha$), then $\Delta \vdash \alpha$. *Can think of as saying* whenever ($\Delta \vDash \alpha$ over $F^2$ where $F \in \mathcal{F}$), we have $\Delta \vdash \alpha$

### Why they do it (how this justifies their choice of axioms)?
First $\mathcal{F}$ itself is merely a subjective opinion of representing euclidean geometry. Granted for historical reasons (Descart) and modern math, it is arguably the best representation, but this is still not a formal justification as to why we condition on $\mathcal{F}$.

Now, assuming $\mathcal{F}$ is a good representation of Euclidean geometry, that is can be taken to be the true representation, **what does 1. and 2. actually do for us**? \

**1.**
This shows that whatever System E proves, is also true under the "true representation". System E does not contradict what the "true representation" says.
**2.**
This shows *anything* that is true under the "true representation", our system can also show this is true. Note if 2. is not true, our system *cannot* show it is false (the negation) or this would contradict soundness. Rather, if 2. is not true we just say that our system may not be able to prove true nor false. What this really gets us is if 2. is true, then our system is as complete as the "true representation"; anything the true representation says is true, our system is also able to say so.

**Aside, why create this thing if we already have a "true representation"?**
- you could argue our own system is more faithful, but if we have an existing representation with $\mathcal{F}$ then literally we can already express (in books 1-4, *not* solid geometry for example) everything euclid writes in this model. The set of axioms is merely a way to classify this $\mathcal{F}$ things into common interfaces we use, and could organize/commucinate why faithful more easily. Perhaps it is like writing binary vs python. binary always works, but it is very hard to tell if it meats the specifications (faithful).

# How I intend to do it
My target is a set of *faithful* axioms. 2. is not related to faithfulness, since how complete the axioms are does not matter when talking abuot how closely we can follow euclid's sentences. We can have a very incomplete language that is still maximally faithful for instance. *1.* is still nice to have as it is *some* sort of justification that these axioms are consistent with the "common" notion of the faithful representation of euclidean geometry.

### Key things to remember
- Each set of books may need its own set of axioms, and "true representation" model as a soundness target.

## Case study for axiom approaches
### 1. naive add everything
**approach**
What if for every single line any time euclid says anything, we just add an axiom. Then a ton of axioms and tons of redunduncies. It will likely still be sound but is there a problem?
**issues**
1. If we axiomatize theorems, then the proof is completely useless. Precisely the issue is that the proof is way longer than it should be.
2. If we axiomize the theorem itself, then having a theorem is kinda dumb, and non-standard.
**issue rebuttal**
1. Our target is faithfulness. Proof longer than it could be is *not* a valid issue. If NL proof is long, we match it even if there is a shorter path.
2. Non-standard is not our target. It is simply faithfulness. I guess there is a problem that our proofs are meaningless while euclid's carry meaning since in his system the proof actually is needed, and ours can be viewed as unfaithful in that sense, though each sentence is stil faithful, and rather some other "higher level meaning/reasoning" is not faithful. Not directly written, but present and can be derived from what is written
3.
### 2. 