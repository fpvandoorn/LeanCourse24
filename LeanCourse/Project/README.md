## Personal Info

Please fill out the following. Fill in the project topic once you have decided.
```
First & last name:
Project topic:
Partner (optional):
```

## Your own project

During the second half of the course you will work on a project in any area of mathematics of your choice. You can put your project files in this folder.

Since a project likely consists of more than 1 file, it will be useful to publish this as a repository on Github.

## Git Instructions

We will be using git via the interface on VSCode. You can also do it from the command line.

### Getting started

* Create an account on `github.com`
* On the command line, run the following two commands, with your name and email substituted in: (you can open a terminal in VSCode with `ctrl+J`/`cmd+J` and clicking `Terminal`)
```
git config --global user.name "Your Name"
git config --global user.email "youremail@yourdomain.com"
```
* In VSCode, open this file and add your name at the top.
* Save all your open files
* Click on the `Source Control` button (left bar, likely the third button from the top).
* Write a small commit message (what you write is not important, but it should not be empty). Press `Commit`.
* Press `Yes` (or `Always`) on the prompt `There are no staged changes to commit. Would you like to stage all changes and commit them directly?`. This will also commit your changes to all other files, which is fine.
* Press `Sync changes`
* Press `OK` (or `OK, don't show again`) when prompted `This action will pull and push commits from and to "origin/master"`
* In the new window, press `Sign in with browser`
* If needed, sign in to Github
* Press `Authorize git-ecosystem`
* You get the message that you don't have permission to push. Press `Create Fork`.
* You should now see your changes at `github.com/<YourGithubUsername>/LeanCourse24`.

### Pushing Later Commits

Pushing another commit after the first one is easy:

* Save all your open files
* Write a small commit message and press `Commit`.
* Press `Sync changes`

Make sure to commit your work at least occasionally (and definitely before giving the presentati

### Pulling commits

After you create your fork I believe that VSCode will not `sync` or `pull` new changes correctly by itself anymore, since it will pull from your fork by default.

To get new changes, do the following:
* Press the three dots icon at the top-right of the `source control` panel `... > Pull / Push > Pull from ... > upstream/master`
* (optionally) press `sync changes`.

Note: After you have created a fork, `git pull` will likely not work anymore from the command line. You can still pull changes from the command line using `git pull upstream master`.
<!--
### Latest Mathlib version

If you want to update to the latest version of Mathlib, you can do this by merging your project into the branch `upstream/newversion`. In this case you have to also run `lake exe cache get!` again.

Detailed instructions in VSCode:
* Press the three dots icon at the top-right of the `source control` panel `... > Pull / Push > Fetch From All Remotes`
* Then do `... > Branch > Merge branch > upstream/newversion`
* Then run `lake exe cache get!` on the command line (you can do this now also within VSCode with `ctrl+shift+P`/`cmd+shift+P` and then start typing `Lean 4 Project: Fetch Mathlib Build Cache` and press enter). -->

### Working with a partner

* If you collaborate with another student on a formalization project, you should still both fork this repository.
* To pull the work from your partner, you can add their repository using `source control` panel `... > Remotes > Add remote ...`. For the URL, you should use `https://github.com/<TheirGithubUserName>/LeanCourse24.git`.
* After this you can pull their work using `... > Pull / Push > Pull from ...`.

### Command-line

If you would like to use Git from your command-line instead, you can use the commands `git pull`, `git add`, `git commit -am "commit message"`, `git push`, `git status`, `git log`, among others. Google for information how to exactly use these commands.


## Formalization Topics

You can choose a topic in any area of mathematics.

A good topic should be
* not yet in mathlib (although it's also fine to give a different proof of something already in mathlib);
* not too hard (don't overestimate how much you can do in your project);
* not require too many prerequisites that are not yet part of mathlib.

On the mathlib website there are some useful pages:
* [topics in mathlib](https://leanprover-community.github.io/mathlib-overview.html)
* [undergraduate topics in mathlib](https://leanprover-community.github.io/undergrad.html)
* [undergraduate topics not yet in mathlib](https://leanprover-community.github.io/undergrad_todo.html
)
* [the full contents of mathlib](https://leanprover-community.github.io/mathlib4_docs/) (use the search in the top right)


Some suggested topics:

<!-- * In **algebraic topology** define CW-complexes and cellular (co)homology.
  Prove some abstract properties of CW-complexes, or compute the cellular (co)homology of some concrete CW-complexes (e.g. spheres). -->

<!-- * In **algebraic topology** prove the adjunction between suspensions and loop spaces. -->

* In **analysis**: the Fourier transform and convolution have been defined in mathlib. Show that the Fourier transform of a convolution is the product of Fourier transforms.

* In **complex analysis** define the winding number of a closed curve. You can either use topological path lifting, or its analytic definition (Cauchy's integral formula exists in mathlib).

* In **complex analysis** define the Laurent series and show that it converges on an annulus.

<!-- * In **differential geometry** define a Riemannian metric and define basic notions of Riemannian geometry. -->

<!-- * In **differential geometry** define smooth `n`-forms and de Rham cohomology. -->

<!-- * [taken] In **Galois theory** define constructible numbers in ℂ and prove that they form the smallest subfield of ℂ closed under square roots. If time permits, prove some famous impossibility results (trisection of an angle / doubling of a cube). Example reference: [David Cox, Galois Theory, Ch 10.1]. -->

<!-- * In **game theory**, define games, pure and mixed strategies, and Nash equilibria. Assuming Brouwer's fixed point theorem, prove that there always exists a Nash equilibrium of mixed strategies. (Brouwer's fixed point theorem is [proven in Lean](https://github.com/Shamrock-Frost/BrouwerFixedPoint/blob/master/src/brouwer_fixed_point.lean#L274), though not yet incorporated in mathlib.) -->

* In **general topology** define some spaces that are typically used for counterexamples, such as the Hawaiian earring, the long line, wild knots or the horned sphere, and (dis)prove some topological properties for them.

<!-- * [taken] In **group theory**, classify all groups of order 8, or if you want a challenge, of order 16. -->

* In **hyperbolic geometry** define the Poincaré model of hyperbolic geometry - either the disc model or the half-plane model (or another model altogether), and show that is satisfies most of Euclid's axioms for geometry, but that the parallel postulate fails.

* In **model theory**: complete types of a language are defined in mathlib. Prove for a countable theory that if there are uncountably many types with `n` free variables, then there are continuum many. Or harder: show that in this case that the theory has continuum many non-isomorphic models.

* In **number theory** solve some diophantine equations. For example: show that there are no nonzero integer solutions to `x^4-y^4=z^2`. Find all solutions to `x^2+y^2=z^3` and to `|2^k-3^l|=1`.

* In **planar geometry** many results are missing. Choose one: the theorem of Ceva's theorem, Desargues's theorem, Feuerbach's theorem, Menelaus's theorem, Morley's trisecor theorem.

<!-- * In **set theory** define club sets, stationary sets and prove Fodor's lemma. -->

## Formalization Tips

Here are some tips for your project.

### Read relevant mathlib files

* There is a rough Mathlib overview here: https://leanprover-community.github.io/mathlib-overview.html
  This can give you an idea what is already in Mathlib.
* Look for related work in the mathlib documentation pages:
  https://leanprover-community.github.io/mathlib4_docs/.
  For some results, the source code will be easier to read.
* The link above is for the newest version of Mathlib. It is possible that some things have changed slightly since the course started. There is also a version of the documentation pages for the exact version of Mathlib this course uses, here: https://florisvandoorn.com/LeanCourse24/docs/
* Step through some of the proofs in Lean.
  You can open the file locally by going to e.g.
  `LeanCourse24/.lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean`
  Note that the `.lake` folder is hidden in VSCode sidebar, but you can navigate through it with `ctrl+O` or `cmd+O`.

### Searching

During class I already discussed searching using the name (using autocomplete or the mathlib docs), or the statement (using `apply?` or `rw?`). Additional options:

* Search Mathlib using natural language: https://leansearch.net/
* Search Mathlib using precise syntax: https://loogle.lean-lang.org/
* Searching on Github directly: https://github.com/leanprover-community/mathlib4
  - This can be useful when searching for a mathematical theorems using its name,
    since the mathlib docs search doesn't search through the documentation of a definition or theorem (only its name).

### Asking for help

* If you have trouble with anything, make sure to ask the tutor or teacher for help during class or office hours.
* If you are stuck on something, try replacing it by `sorry` and move on to the next part until you can ask about it.

* You are allowed to ask any AI for help. I do not necessarily recommend using them,
  often their suggestions are not very helpful.
  * Github copilot can sometimes help with stating lemmas or proving a set.
  * ChatGPT knows some Lean, but it bad at proofs and often suggests outdated Lean 3 syntax

### Writing definitions

It is useful to find a definition that already exists in mathlib and is similar to what you want.
Then you can mimic the structure of that definition.
This can also be useful in deciding whether to use `def`, `structure` or `class`.

## Presentations

During January, you should give a presentation on your project during class.
The presentation should be 20-25 minutes, plus 5 minutes for questions; it should be 30-40 minutes if you do the project with a partner.

During your presentation, you can discuss the following (but you don't have to treat every point)
* Explain the mathematical content of your formalization
* Show some of the formalized work (for example if you have found interesting way to state a definition, or the statement of the theorem you proved).
* What went easily when formalizing? What was hard? Were any tools or tactics particularly useful, or did you miss a specific tactic?

You do not have to finish your project before your presentation, so your presentation is probably about the ongoing work. Projects are due February 9 (roughly 1 week after classes end).
