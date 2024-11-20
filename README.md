# Bonn Lean Course WiSe 24/25

## In this repository

You will find the Lean files in the `LeanCourse` directory:
* The `Lectures` folder contains all lectures (I will post 2 versions of each lecture file: the one before
* The `Assignments` folder contains the assignments that you have to hand in via eCampus.
* The `MIL` folder contains the exercises from the book Mathematics in Lean. You can find the textbook online here:
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
(or as a
[pdf document](https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf)).

## Installation

* You have to install Lean, and two supporting programs: Git and VSCode. Follow these [instructions](https://docs.lean-lang.org/lean4/doc/quickstart.html) to do this.

* This will guide you to install VSCode (a text editor which supports Lean), git (a version control system) and elan (the Lean package manager).

* (On Windows, antivirus programs can cause slowdowns or errors when downloading a Lean project. Consider temporarily disabling your antivirus program in the step *Set up Lean 4 project*)

* In the step **Set up Lean 4 project** click on **Download an existing project** (third bullet point). Choose `Git repository URL`, enter `https://github.com/fpvandoorn/LeanCourse24` and then select a folder where you want to download this repository, and specify a folder name. Then press `Create project folder` and wait a few minutes.

* When you have downloaded the repository a message appears allowing you to open the project folder.
To test that everything is working, open the repository and open the file `LeanCourse/Test.lean`.
The file should be ready a few seconds later. If you see a blue squiggle under `#eval`, Lean is running correctly.

* A useful (but optional) extension is the VSCode extension `Error Lens`. If you install this, you will see messages from Lean right in the file where you're typing.

## Troubleshooting

Note: To get this repository, you will need to download Lean's mathematical library, which takes about 5 GB of storage space.

It might be tricky to get Lean running on a laptop that is more than 10 years old or on a chromebook, since Lean does use a moderate amount of recourses.
You can still run Lean in your browser by using Codespaces or Gitpod, see the the instructions at the bottom of this file.

* If you get errors such as `curl: (35) schannel` or `uncaught exception: no such file or directory (error code: 2)` take a look [here](https://leanprover-community.github.io/install/project.html#troubleshooting).

## Update repository

If you want to get the latest version of this repository (e.g. the latest exercises), then you can pull the changes. (I mentioned before you have to commit first, this is not, in fact, necessary)

You can do this either via a terminal (`git pull`)
or via VSCode, in the `Source Control` tab (third icon in the top-left, or `ctrl+shift+G`/`cmd+shift+G`),
under `⋯` (More actions) you can click `Pull` to get the latest changes.

<!-- You can commit by writing a non-empty commit message and then pressing `Commit` (you can answer "Yes" or "Always" when it asks you if you want to stage all changes.).  -->
<!-- Troubleshooting: if you have configured git pull to use rebase, then you
have to commit the changes first.  -->

Note: you should *not* press `Sync`, since that will try to upload your changes to the assignment files to GitHub (you don't have the rights to do this).

We might at some point update the version of Lean for the repository (we will tell you when this happens). In that case, after running `git pull` you have to get the new Mathlib cache. In this case, *do not* restart a Lean file (which will prompt Lean to rebuild Mathlib on your laptop).
Instead press `∀ > Project Actions... > Fetch Mathlib Build Cache` and wait for the cache to download.
After it has finished, you might have to restart the Lean file, and then Lean should be compiling your file in less than a minute.

If this fails, try the following steps:
* Close VSCode (if it is open)
* In your terminal, in the `LeanCourse24` folder, run `lake exe cache get!` (or `~/.elan/bin/lake exe cache get!` if `lake` cannot be found).
* Wait until the command finishes with downloading and decompressing. If you get an error, run it again.
* Now you can reopen VSCode and restart the file (if prompted).

## Temporary ways to use Lean

You can temporarily use Codespaces or Gitpod if you have trouble installing Lean locally.

### Using Codespaces

You can temporarily play with Lean using GitHub codespaces. This requires a GitHub account, and you can only use it for a limited amount of time each month. If you are signed in to GitHub, click here:

<a href='https://codespaces.new/fpvandoorn/LeanCourse24' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

* Make sure the Machine type is `4-core`, and then press `Create codespace`
* After 1-2 minutes you see a VSCode window in your browser. However, it is still busily downloading mathlib in the background, so give it another few minutes (5 to be safe) and then open a `.lean` file to start.

### Using Gitpod

Gitpod is an alternative to codespaces that is slightly inconvenient, since it requires you to verify your phone number.

Click this button to get started:

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/fpvandoorn/LeanCourse24)

This creates a virtual machine in the cloud,
and installs Lean and Mathlib.
It then presents you with a VS Code window, running in a virtual
copy of the repository.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get!` as above.

Gitpod gives you 50 free hours every month.
When you are done working, choose `Stop workspace` from the menu on the left.
The workspace should also stop automatically
30 minutes after the last interaction or 3 minutes after closing the tab.

To restart a previous workspace, go to [https://gitpod.io/workspaces/](https://gitpod.io/workspaces/).


## Links

* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
* [Lean website](https://www.lean-lang.org/)
* [Mathlib website](https://leanprover-community.github.io/)
* [Topics in Mathlib](https://leanprover-community.github.io/mathlib-overview.html)
* [API documentation for this course](https://florisvandoorn.com/LeanCourse24/docs/)
* [latest Mathlib API documentation](https://leanprover-community.github.io/mathlib4_docs/)

Some exciting projects using Lean:

* Interesting finished Lean projects: [Liquid Tensor Experiment](https://github.com/leanprover-community/lean-liquid), [Freiman-Ruzsa Conjecture](https://teorth.github.io/pfr/), [Independence of the continuum hypothesis](https://flypitch.github.io/)
* Interesting ongoing Lean projects [Fermat's Last Theorem](https://imperialcollegelondon.github.io/FLT/), [Carleson's theorem](https://florisvandoorn.com/carleson/), [Equational Theories project](https://teorth.github.io/equational_theories/)
* [AlphaProof](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/) did well at the international mathematics olympiad using Lean.
