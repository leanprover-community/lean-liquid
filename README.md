# Liquid Tensor Experiment

[![](https://github.com/leanprover-community/lean-liquid/actions/workflows/build.yml/badge.svg?branch=master)](https://github.com/leanprover-community/lean-liquid/actions/workflows/build.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/leanprover-community/lean-liquid)

For the eponymous blogpost by Peter Scholze which started it all: see https://xenaproject.wordpress.com/2020/12/05/liquid-tensor-experiment/.

The main aim of this community-owned repository is to *digitise* some mathematical definitions, theorem statements and theorem proofs. Digitisation, or formalisation, is a process where the source material, typically a mathematical textbook or a pdf file or website or video, is transformed into definitions in a target system consisting of a computer implementation of a logical theory (such as set theory or type theory).

## The source.

The main "source" definitions, theorems and proofs in this repository are all taken from Scholze's Bonn lecture notes [Analytic.pdf](https://www.math.uni-bonn.de/people/scholze/Analytic.pdf) explaining some of his work with Clausen on the theory of solid and liquid modules, and on their development of a new approach to certain proofs in complex analytic geometry.

## The target

The formal system which we are using as a target system is Lean's dependent type theory. Lean is a project being developed at Microsoft Research by Leonardo de Moura and his team. Our formalisation could not have even started without a major classical mathematical library backing it up, and so we chose Lean 3 as the engine behind the project. Although Lean 4's type theory is the same as Lean 3's type theory, it currently lacks the mathematical infrastructure needed for this project.

## Brief overview of the project

Our interpretation of the blog post and TeX file was that the challenge was to formalise `Analytic 9.1` (i.e. Theorem 9.1 of the pdf) in Lean. We chose to use Lean 3 because of the advanced state of its classical mathematics library `mathlib`, an essential ingredient.

When the project started, it was immediately noticed that there was a "sub-boss" in the form of `Analytic 9.4`, a far more technical theorem involving a completely different class of objects and which Scholze was claiming was a sufficiently powerful stepping stone. The project then split intwo two sub-projects:
"Prove `9.4`" and "Prove that `9.4` implies `9.1`".

An important intermediate achievement was the completion of a [blueprint](https://leanprover-community.github.io/liquid/) for the proof of `9.4` and the related `9.5`. The blueprint was a guide which was comprehensible to mathematicians who had no Lean training, whilst also being a visual guide to where progress was needed during the formalisation process.

The preliminary announcement of a proof of Theorem 9.4 was made on 28th May 2021, by Johan Commelin and his team from the Lean prover community.
The second half of the project was [completed](https://leanprover-community.github.io/blog/posts/lte-final/) on 14th July 2022.
Together, the two components give a formal verification of Theorem 9.1 of [`Analytic.pdf`](https://www.math.uni-bonn.de/people/scholze/Analytic.pdf).

## The formal statement of `Analytic 9.4`.

The statement can be found in [`src/liquid.lean`](https://github.com/leanprover-community/lean-liquid/blob/master/src/liquid.lean#L37)

```lean
theorem first_target :
  ∀ m : ℕ, ∃ (k K : ℝ≥0) [fact (1 ≤ k)] (c₀ : ℝ≥0),
  ∀ (S : Type) [fintype S] (V : SemiNormedGroup.{0}) [normed_with_aut r V],
    ​((BD.data.system κ r V r').obj (op $ of r' (Lbar r' S))).is_weak_bounded_exact k K m c₀ := _
```

See [`src/liquid.lean`](https://github.com/leanprover-community/lean-liquid/blob/master/src/liquid.lean#40)
for details on how to read this statement.

## The formal statement of `Analytic 9.1`.

The statement can be found in [`src/challenge.lean`](https://github.com/leanprover-community/lean-liquid/blob/master/src/challenge.lean#L28)

```lean
variables (p' p : ℝ≥0) [fact (0 < p')] [fact (p' < p)] [fact (p ≤ 1)]

theorem liquid_tensor_experiment (S : Profinite.{0}) (V : pBanach.{0} p) :
  ∀ i > 0, Ext i (ℳ_{p'} S) V ≅ 0 :=
```

## How to browse this repository

### Blueprint

Below we explain how to engage with the Lean code directly.
We also provide a [blueprint](https://leanprover-community.github.io/liquid/)
including two [dependency](https://leanprover-community.github.io/liquid/dep_graph_section_1.html)
[graphs](https://leanprover-community.github.io/liquid/dep_graph_section_2.html)
of the main ingredients in the repository.
All material in the blueprint is cross-referenced with the Lean formalization using hyperlinks.

### Getting the project

At the moment, we support two ways of browsing this repository:
Either via Gitpod or by using a Lean development environment.

Crucially, both methods will allow you to introspect Lean's "Goal state" during proofs,
and easily jump to definitions or otherwise follow paths through the code.

Gitpod provides an online Lean environment, but requires a GitHub account
and might have weaker performance than a local installation.
To use it, simply click the Gitpod button at the top of this Readme file.

To install a Lean development environment on your computer please use the
[installation instructions](https://leanprover-community.github.io/get_started.html#regular-install)
to install Lean and a supporting toolchain.
After that, download and open a copy of the repository
by executing the following command in a terminal:
```
leanproject get lean-liquid
code lean-liquid
```
For detailed instructions on how to work with Lean projects,
see [this](https://leanprover-community.github.io/install/project.html). The script `scripts/get-cache.sh`
in the folder `lean-liquid` will download the `olean` files created by our continuous integration. This
will save you some time by not havig to do `leanproject build`.

### Reading the project

With the project opened in VScode,
you are all set to start exploring the code.
There are two pieces of functionality that help a lot when browsing through Lean code:

* "Go to definition": If you right-click on a name of a definition or lemma
  (such as `Lbar`, or `Tinv_continuous`), then you can choose "Go to definition" from the menu,
  and you will be taken to the relevant location in the source files.
  This also works by `Ctrl`-clicking on the name.
* "Goal view": in the event that you would like to read a *proof*,
  you can step through the proof line-by-line,
  and see the internals of Lean's "brain" in the Goal window.
  If the Goal window is not open,
  you can open it by clicking on one of the icons in the top right hand corner.

### Important files in the project

* All the Lean code (the juicy stuff) is contained in the directory `src/`.
* The file `src/challenge.lean` contains the statement of the main theorem.
* The file `src/liquid.lean` contains the statement of the first target (the first half of the project).
* The directory `src/examples/` contains Lean files that explain the main ingredients in the statement of the main theorem.
  These files should form convincing evidence that we did not make a mistake in formalizing the necessary definitions.
* The directory `src/for_mathlib/` contains preliminary material that is gradually being moved to mathlib, the main library of mathematics for Lean.

## Brief note on type theory

Lean is based on type theory,
which means that some things work slightly differently from set theory.
We highlight two syntactical differences.

* Firstly, the element-of relation (`∈`) plays no fundamental role.
  Instead, there is a typing judgment (`:`).

  This means that we write `x : X` to say that "`x` is a term of type `X`"
  instead of "`x` is an element of the set `X`".
  Conveniently, we can write `f : X → Y` to mean "`f` has type `X → Y`",
  in other words "`f` is a function from `X` to `Y`".

* Secondly, type theorists do not use the mapsto symbol (`↦`),
  but instead use lambda-notation.
  This means that we can define the square function on the integers via
  `λ x, x^2`, which translates to `x ↦ x^2` in set-theoretic notation.
  For more information about `λ`, see the Wikipedia page on
  [lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus).

For a more extensive discussion of type theory,
see the dedicated
[page](https://leanprover-community.github.io/lean-perfectoid-spaces/type_theory.html)
on the perfectoid project website.

## Source reference

`[Analytic]` : http://www.math.uni-bonn.de/people/scholze/Analytic.pdf

[Analytic]: http://www.math.uni-bonn.de/people/scholze/Analytic.pdf
