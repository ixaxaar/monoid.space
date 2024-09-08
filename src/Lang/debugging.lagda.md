****
[Contents](contents.html)
[Previous](Lang.syntaxQuirks.html)
[Next](Types.introduction.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Debugging Agda](#debugging-agda)
  - [Holes](#holes)
  - [Features](#features)
    - [Global commands](#global-commands)
    - [Goal-specific commands](#goal-specific-commands)
    - [Commands working in the context of a specific goal](#commands-working-in-the-context-of-a-specific-goal)
  - [Text editor support](#text-editor-support)
  - [Useful Agda-mode commands](#useful-agda-mode-commands)
  - [Practical Debugging Examples](#practical-debugging-examples)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Debugging Agda

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module Lang.debugging where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
```

Debugging and tooling are arguably the most vital parts of the development process and a language ecosystem. Tools tend to help developers figure out issues and assist them in the entire process. Agda has a small set of indispensable tools for such purposes. We look at how to use some of them to make our lives easier.

## Holes

The Agda compiler supports type checking and providing hints while writing code. Unknown types can be represented with a placeholder `?` and the compiler can help deduce the type.

```agda
data _even : Nat → Set where
  ZERO : zero even
  STEP : ∀ x → x even → suc (suc x) even

proof₁ : suc (suc (suc (suc zero))) even
proof₁ = ?
```
The Agda compiler hints that the `?` should be of type `4 even`. This placeholder `?` is called a **hole**.

Holes are particularly useful when you're not sure how to proceed with a proof or implementation. They allow you to leave parts of your code unfinished while still being able to type-check the rest.

## Features

Agda supports various `Interaction` commands to provide several features via the `agda --interaction` command. This implements a client-server protocol whereby a client can communicate with the Agda compiler to do various tasks on the source files.

Agda supports the following commands:

### Global commands

| Name                                 | Description                                                                                    | Internal name               |
|--------------------------------------|------------------------------------------------------------------------------------------------|-----------------------------|
| load                                 | Load a file and type check it.                                                                 | `Cmd_Load`                  |
| compile                              | compile a file using the various Agda backends (`GHC`, `GHCNoMain`, `LaTeX`, `QuickLaTeX` etc) | `Cmd_compile`               |
| abort                                | abort the current operation, do nothing otherwise                                              | `Cmd_abort`                 |
| toggle-display-of-implicit-arguments |                                                                                                | `ToggleImplicitArgs`        |
| show-constraints                     | Show constraints or goals                                                                      | `Cmd_constraints`           |
| solve-constraints                    | Solve all constraints in a file                                                                | `Cmd_solveAll`              |
| show-goals                           | Show all goals in a file                                                                       | `Cmd_metas`                 |
| search-about                         | Search about a keyword                                                                         | `Cmd_search_about_toplevel` |

### Goal-specific commands

| Name                | Description                                                         | Internal name              |
|---------------------|---------------------------------------------------------------------|----------------------------|
| why-in-scope        | Explain why a keyword is in scope                                   | `Cmd_why_in_scope`         |
| infer-type          | Infer type                                                          | `Cmd_infer`                |
| module-contents     | List all module contents                                            | `Cmd_show_module_contents` |
| compute-normal-form | Compute the normal form of either selected code or given expression | `Cmd_compute`              |

### Commands working in the context of a specific goal

| Name                        | Description                                                 | Internal name                 |
|-----------------------------|-------------------------------------------------------------|-------------------------------|
| give                        | Fill a goal                                                 | `Cmd_give`                    |
| refine                      | Refine. Partial give: makes new holes for missing arguments | `Cmd_refine_or_intro`         |
| auto                        | Automatic proof search, find proofs                         | `Cmd_auto`                    |
| case                        | pattern match on variables (case split)                     | `Cmd_make_case`               |
| goal-type                   | Goal type                                                   | `Cmd_goal_type`               |
| context                     | Context of the goal                                         | `Cmd_context`                 |
| goal-type-and-context       | Type and context of the goal                                | `Cmd_goal_type_context`       |
| goal-type-and-inferred-type | Infer goal type and the context of the goal                 | `Cmd_goal_type_context_infer` |

## Text editor support

The interaction commands mentioned above can be tied to text editors and IDEs to provide additional assistance for programmers. Such integrations exist for the following text editors:

- Emacs - developed first, has tightest integration [Emacs mode](https://agda.readthedocs.io/en/v2.5.2/tools/emacs-mode.html)
- Atom - [agda-mode](https://atom.io/packages/agda-mode)
- VSCode - [vscode-agda](https://github.com/banacorn/vscode-agda)
- vim - [agda-vim](https://github.com/derekelkins/agda-vim)

There is discontinued support for [sublime](https://github.com/banacorn/agda-mode-st3) and [eclipse](https://pdfs.semanticscholar.org/b7f9/32609298debd21398d54e13c864e26a03ac1.pdf).

## Useful Agda-mode commands

```markdown
C-c C-l   load (type checking)
C-c C-f   forward (jump to next hole)
C-c C-b   backward (jump to previous hole)
C-c C-d   deduce (type of expression)
C-c C-n   normalize (evaluate expression)
```

```markdown
Commands inside a hole
C-c C-,   information about the hole
C-c C-d   deduce (type of contents of hole)
C-c C-Space   give (checks whether the term in the hole has the right type and if it has, replaces the hole with the term)
C-c C-c   case split (pattern match on variables)
C-c C-r   refine (one step further)
C-c C-a   auto (try to find a solution)
```

Agda-mode for Emacs can be installed using:

```bash
agda-mode setup
```

This entire project can be loaded into Emacs like:

```bash
emacs ./contents.lagda.md
```

followed by loading `agda-mode` by typing `space` `space` `agda-mode`. Using [spacemacs](http://spacemacs.org/) is recommended.

## Practical Debugging Examples

Let's look at a couple of practical examples to illustrate how to use Agda's debugging features:

1. Using holes to develop a proof incrementally:

```agda
+-comm : (m n : Nat) → m + n ≡ n + m
+-comm zero n = ?
+-comm (suc m) n = ?
```

Here, we've left holes in our proof of commutativity of addition. We can use Agda-mode commands to:
- Check the type of each hole (C-c C-,)
- Try auto-completion (C-c C-a)
- Refine the proof step by step (C-c C-r)

2. Using case splits:

```agda
data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not x = ?
```

With the cursor on `x`, we can use C-c C-c to perform a case split, which will generate:

```agda
not' : Bool → Bool
not' true = ?
not' false = ?
```

These practical examples demonstrate how Agda's interactive features can assist in developing proofs and functions step by step, making the development process more manageable and insightful.

****
[Type Theory - Introduction](./Types.introduction.html)
