### Constraints
First these are only set in motion *after* I have finished all of the formalization not rn but this is for me to have a clear picture.

These are things, where if not satisfied, our metric will report N/A.

1. Relations cannot be removed
2. Constant symbols similarily removed
3. functions cannot be removed

Note this essentially means that *only* $\Delta$, the set of system E formulae (what we call system E axiosm loosely) can we remove elements from. Though we can always add though this should always be unecessary.
**Reason for these restrictions**
adding a relation is fine. Faithfulness is evaluated on the mapping and adding syntax cannot change these mappings. However removing some things could be bad since these could be within the map phase which cannot change. So adding things should be fine. is removing fine? In other words are there any cases where there is one of 1--3 that is *not* in any mapping? that would be weird actually and imply this thing is not needed in the language. In practice we should never hae this case and it should be exactly that everything in 1--3 *is used at some point in one of the mappings* and therefore the rule of *do not remove anything* should be universally valid for 1--3, and thus we claim so. If it is that we do not need to remove something, then this suggests a mapping error on my part or axiom error on my part. Basically we cannot remove anything is the verdict.

### Metrics we measure
Let $\mathfrak{M}$ to be a structure that *should* model the specific set of propositions we are targetting. For example can use $\mathfrak{M}$ to be the cartesian coordinates in 2D over fields for the early books as Tarski did. Note that *should* is judged by a human expert / historical context and is *not formally justified*, and rather we claim it is (at least somewhat faithful) due to human agreement.

Let $\Delta$ denote the set of (non-logical) axioms for this formalizations

Let $\mathcal{S}$ is the set of all symbols (uniqueness not required so not a set) of $\Delta$. For example if $\Delta=\{P(a, b) \to Q(a), T(a) \to L(b)\}$, the $\mathcal{S}=\{P, a, b, Q, a, T, a, L, b\}$ something like that though this is still a vague definition. Also for any definitions they must be expanded to get the symbols.

1. *$\mathfrak{M}$--soundness*: For any formula $\alpha$, whenever $\Delta \vdash \alpha$ we have $\mathfrak{M} \vDash \alpha$
2. $|\mathcal{S}|$ \
~~3. *$\mathfrak{M}$--completeness*: For any formula $\alpha$, whenever $\mathfrak{M} \vDash \alpha$ we have $\Delta \vdash \alpha$~~
~~4. *${\Delta}$-completeness*: For any formula $\alpha$, $\Delta \vdash \alpha$ or $\Delta \vdash \neg \alpha$~~
~~5. *$\Delta$--consistency*: $\Delta \nvdash \neg (\alpha \to \alpha)$~~

**Why cancel 3 4 and 5** \
5. is not checkable in general (Godel) so we remove this for simplicity. 3 implies 4 (I think) and 3 is out of scope for now and we leave to future work.s
**Note for 1** \
For 1, it suffices to show (and clearly necessary) $\mathfrak{M} \vDash \Delta$ since for any $\alpha$ if $\Delta \vdash \alpha$, then clearly $\Delta \vDash \alpha$ by soundness theorem and since we just showed $\mathfrak{M} \vDash \Delta$ we can then conclude $\mathfrak{M} \vDash \alpha$

### Why I claim 1--3 determine how "good" axioms are
**1 and 2**

These I claim are actually necessary conditions for faithful set of axioms. So these are really about the faithfulness part. My reasoning is this; huanity has mostly agreed that these eulidean fields are a faithful model (Descartes, modern "euclidean geometry" literally refers to using these models, tarski did it this way, Avigad, etc.). Thus taking this model as groud truth faithfulness, then if $\Delta$ (and the language) is faithful, then it *must* agree on every statement with our system (language ad axioms), because the faithful model (G.T.) determines the "validity" of every statement so we must agree to this or we would be creating a contradiction.

Essentially I am claiming that the faithful model is true as an axiom (or assume this), and therefore we must agree with it.

As a side note, it may very well be the case that we do not have some "agreed upon faithful model" so this strategy is *not* applicable in general, but again, this is a *starting point* (not done before) for axiom-creating benchmark and works for our Elements case. Like we have to start somewhere.

**3**
This one is not about faithfulness, but about the general "good" axiom.

Here, generally "less" axioms are better because we do not want to assume to much to be true as this would create more "trust-me-bro" things and that is generally not good. Measuring only number of axiosm is bad since we can have one massive conjuction of literals so we measure symbols instead.

**Final Score**
The final score is a combination of 1, 2, and 3 where 1, 2 are in $\{1, 0\}$ (true/false) while the lower 3 is the better. and true is better for both 1 and 2.

### Metrics I target in *my* attempt.
First this is *not* the best version, and merely a starting point. I will *not* aim for item 2 (though tarski was able to do this). I will aim for 1 and making 3 small.