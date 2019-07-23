# PUMPKIN PATCH User Guide

This is a prototype plugin for finding patches for broken Coq proofs.
To use PUMPKIN, the programmer modifies a single proof script to provide 
an _example_ adaptation of a proof to a change. PUMPKIN generalizes this example 
into a _reusable patch_ which can be used to fix other broken proofs.

This is a research prototype, so it is definitely not production-ready.
With that in mind, I hope that by getting it out into the open I can
contribute what I've learned so far. You can use it on the example proofs and
you can extend it if you are interested. Don't hesitate to reach out
if you have any questions. Similarly, please let me know if anything I have mentioned
in this user guide does not work or is unclear.

Reading the [paper](http://tlringer.github.io/pdf/pumpkinpaper.pdf) may help if you are interested
in understanding the internals of the tool. The paper links to a release that captures
the code as it was when we wrote the paper. The [talk video](http://www.youtube.com/watch?v=p-V9oerg5DU)
may also be helpful.

## Building PUMPKIN

The plugin works for Coq 8.8. There are branches for Coq 8.5 and 8.6, which we are no
longer maintaining.

```
cd plugin
./build.sh
```

## Using PUMPKIN

We will walk through a simple example. You can follow along this example
by looking at the code in [Example.v](/plugin/coq/Example.v).

Suppose you have proven a theorem `old1`:

```
Theorem old1:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1.
Proof.
  ...
Qed.
```

You then realize that the conclusion of `old1` is weak, so you strengthen it
to the theorem `new1`:

```
Theorem new1:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  ...
Qed.
```

You would like to port a proof that applies `old1`:

```
apply old1.
```

To instead apply `new1`:

```
... apply new1.
```

To do this using PUMPKIN, load the file `Example.v` (feel free to use your favorite IDE here instead of `coqtop`):

```
coqtop -load-vernac-source plugin/coq/Example.v
```

Next, import the plugin:

```
Require Import Patcher.Patch.
```

Invoke the plugin to produce a patch:

```
Patch Proof old1 new1 as patch.
```

This defines a term `patch`. Let's check the type of `patch`:

```
Check patch.
```
This should produce this output:

```
patch
  : forall n m p : nat, n <= m -> m <= p -> n <= p -> n <= p + 1
```

In other words, `patch` is a function that takes the conclusion of `new1` back to the conclusion of `old1`. 
Then anywhere we have a proof that applies `old1`:

```
apply old1.
```

We can use `patch` to port this proof to use `new1` instead:

```
apply patch. apply new1.
```

### Applying Patches

One thing that you'll notice is that in the example above, we applied this patch by hand.
For now, PUMPKIN does not automatically apply patches that it finds. We are working on a better user experience.

In the meantime, we suggest adding patches to a hint database. For example, instead of writing this:

```
apply patch. apply new1.
```

You can instead add `patch` to your hints:

```
Hint Resolve patch.
```

You can then port your proof to use ```new1``` with no additional changes:

```
apply new1.
```

### Git Integration

The [PUMPKIN-git](http://github.com/uwplse/PUMPKIN-git) interface searches for patches across
Git revisions. It also automatically removes the reference to the old definition.
Please see the repository for more details.

### Pattern Matching and Fixpoints

By default, PUMPKIN has very limited support for proofs that use pattern matching and fixpoints.
However, the `Preprocess` command by Nate Yazdani automatically converts simple pattern matching and fixpoints
into induction principles, which PUMPKIN does support. You can `Preprocess` individual proofs:

```
Preprocess old as old'.
Preprocess new as new'.
Patch Proof old' new' as patch.
```

Or you can preprocess entire modules:

```
Preprocess Module Old as Old'.
Preprocess Module New as New'.
Patch Proof Old'.old New'.new as patch.
```

See [Preprocess.v](/plugin/coq/Preprocess.v) and [PreprocessModule.v](/plugin/coq/PreprocessModule.v) for examples
of how to use these commands. There are also proofs in [Regress.v](/plugin/coq/Regress.v) and [IntegersNew.v](/plugin/coq/IntegersNew.v) 
that demonstrate its use with `Patch Proof`.

### Cutting Lemmas

For some kinds of proofs, PUMPKIN needs extra guidance to search for a patch.
The hope is that this will eventually be unecessary, but for now, it is a way to work around
limitations in the tool.

You can provide this guidance by cutting a lemma. For example, consider the proofs of `bin_to_nat_pres_incr` in [Induction.v](https://github.com/uwplse/PUMPKIN-PATCH/blob/master/plugin/coq/Induction.v). These proofs each 
contain proofs of inline lemmas:

```
assert (H : forall a :nat, S (a + S (a + 0)) = S (S (a + (a + 0)))).
```

```
assert (H : forall a :nat, S (a + S a) = S (S (a + a))).
```

PUMPKIN cannot yet automatically determine that the patch between the versions of `bin_to_nat` referenced
by each `bin_to_nat_pres_incr` is in the difference of this inline lemma.
However, we can guide it there:

```
Definition cut :=
  forall (a : nat),
    S (a + S a) = S (S (a + a)) ->
    S (a + S (a + 0)) = S (S (a + (a + 0))).
    
Patch Proof blindfs_induction.bin_to_nat_pres_incr bin_to_nat_pres_incr cut by (fun (H : cut) b0 => H (bin_to_nat b0)) as patch.
```

The interface for this is a little tricky; we plan to improve this significantly, since it is a useful way to work
around limitations.

### Support & Limitations

Speaking of limitations: PUMPKIN is a research prototype, and so it is currently limited in the 
kinds of proofs and changes it supports. PUMPKIN is best equipped to handle changes in conclusions of inductive proofs.
It has introductory support for changes in hypotheses.
It also supports certain changes in definitions (for example, changes in a constructors
of an inductive type that a proof inducts over, or changes in a case of a fixpoint that a theorem applies),
and some other styles of proofs (for example, simple applicative proofs, or
proofs that apply constructors).

PUMPKIN does not yet support structural changes like adding new hypotheses,
adding constructors or parameters to an inductive type, or adding cases to a fixpoint.
PUMPKIN has very limited support for proofs using logic specific to decidable domains
(such as proofs that use `omega`) and nested induction.
Supporting all of these features is on our roadmap.

For now, if PUMPKIN fails to find a patch, it's likely due to features that are not yet implemented.
In any case, if you encounter any error or failure, please cut an issue with a reproducable example, since we can
determine whether the error is a bug or an unimplemented feature, and use it as an eventual test case.
With that in mind, we are a small research team, so it may take time to implement all of these features.
If you would like to contribute directly to the plugin, feel free to cut a pull request.

## Bonus Functionality

### Proof Optimization

Proof patching can be used to optimize proofs as well. Optimization removes extra induction
and fixpoints (for fixpoints, you need to run `Preprocess` first). You can run this command
by running:

```
Optimize Proof Term slow as fast.
```

There are some examples of this [here](/plugin/coq/Optimization.v). Note that `Optimize Proof Term` is implemented
on top of `Patch Proof`, and so will face the same limitations.

### Core Components as Commands

The core of PUMPKIN is a set of five core components. We expose four of those components as commands:

1. `Invert trm as id`: given `trm : ... -> T1 -> T2`, search for an inverse term `id : ... -> T2 -> T1`
2. `Specialize (fun args => f args) as id)`: apply `f` to `args`, reduce the result, and define this as `id`
3. `Abstract trm to typ as id`: abstract `trm` to a term `id : typ`
4. `Factor trm using prefix id`: given `trm : T1 -> Tn`, search for factors `id_1: T1 -> T2`, ... , `id_n-1: Tn-1 -> Tn`

### Theorem Patching

There is also an experimental theorem patching command:

```
Patch Theorem oldT1 newT1 oldT2 as newT2.
```

This essentially does dependent substitution of `oldT1` with `newT1` inside of `oldT2`, then defines the result as `newT2`.
Support for this is very preliminary. You can find some examples [here](/plugin/coq/Theorem.v).

## Examples

There are some example proofs to help you get started using PUMPKIN.
You can find these in the [coq](/plugin/coq) directory.
You can load them using `coqc`, `coqtop`, or your favorite IDE.

The relevant examples are as follows:
1. [Example.v](/plugin/coq/Example.v) and [Regress.v](/plugin/coq/Regress.v): Simple changes in conclusions of inductive proofs
2. [Reverse.v](/plugin/coq/Regress.v): Isomorphic changes in conclusions of inductive proofs
3. [Cex.v](/plugin/coq/Cex.v): Example of the proof from Section 3 of the paper for which the footnote does not hold
4. [IntegersOld.v](/plugin/coq/IntegersOld.v) and [IntegersNew.v](/plugin/coq/IntegersNew.v): Case study from Section 4.1 of the paper
5. [Inductive.v](/plugin/coq/Inductive.v): Case study from Section 4.2 of the paper
6. [divide.v](/plugin/coq/divide.v): Case study from Section 4.3 of the paper
7. [Variants.v](/plugin/coq/Variants.v): Patch Generation Suite from Section 6 of the paper
8. [Abstract.v](/plugin/coq/Abstract.v): Example of using the abstraction command
9. [Theorem.v](/plugin/coq/Theorem.v): Example fo the experimental theorem patching command
10. [Hypotheses.v](/plugin/coq/Hypotheses.v): Very simple changes in hypotheses.

## Extending PUMPKIN

If you've never written a Coq plugin before, you might want to check out
and toy with my [starter plugin](http://github.com/uwplse/CoqAST/) first. 

To get an idea of how the code is structured, I highly recommend reading Section 5 of the paper
and following along in the code. The entry-point to the code is [patcher.ml4](/plugin/src/patcher.ml4). 
You can add new commands there. You can also extend the patch finding procedure or see what it calls out to and modify that.
There is a useful debugging function in [differencing.ml](/plugin/src/core/components/differencing/differencing.ml);
if you are modifying the tool, you may want to use it.

Minor note: .ml4 files don't appear to work with a lot of emacs OCaml plugins.
You can run tuareg-mode manually on .ml4 files.

## Contributors

This plugin is maintained by Talia Ringer with help from Nate Yazdani.
John Leo and Dan Grossman have made conceptual contributions.

The following community members have also contributed to the code:
1. Emilio Jesús Gallego Arias
2. Your name here!
