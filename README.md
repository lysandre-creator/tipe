# LTL Model Checking Applied to a Puzzle Game

> TIPE (independent research project), French preparatory class (CPGE, MPI track), individual work.

This project implements **LTL model checking from scratch**: given a system (modeled as a Kripke structure) and a property written as a Linear Temporal Logic formula, it automatically decides whether the system satisfies the property — and if not, produces a concrete counter-example. As a test case, it solves the classic **wolf, goat and cabbage river-crossing puzzle**, showing that a puzzle traditionally solved by hand or by graph search can instead be solved by encoding it as a verification problem.

## The puzzle

A farmer must ferry a wolf, a goat, and a cabbage across a river. The boat only carries the farmer plus one item at a time. Left unsupervised, the wolf eats the goat, and the goat eats the cabbage. The question: is there a sequence of crossings that gets everyone across safely?

This is normally solved with a short, ad-hoc graph search. The point of this project is different: instead of writing a search tailored to this one puzzle, the puzzle is encoded as a generic verification question — "**does there exist a path in this state graph along which this temporal property eventually holds?**" — and a general-purpose algorithm answers it, without knowing anything about wolves or boats.

## Background: LTL and model checking

**Model checking** is a formal verification technique: given a model of a system's possible behaviors and a specification of what it should (or shouldn't) do, an algorithm exhaustively checks whether every behavior satisfies the specification. It's widely used to verify hardware, protocols, and safety-critical software, where "testing a few cases" isn't good enough.

The system's behavior is modeled as a **Kripke structure**: states, transitions between them, and, in each state, which atomic propositions are true (e.g. `wolf_on_left`, `goat_on_right`).

The specification is written in **Linear Temporal Logic (LTL)** — propositional logic extended with operators over time, such as:
- `X φ`: φ holds at the *next* step
- `F φ`: φ holds *eventually*
- `G φ`: φ holds *always* (globally)
- `φ U ψ`: φ holds *until* ψ becomes true

For the puzzle, the property checked is roughly *"eventually, everyone is on the right bank"* — `F (all_on_right)`.

## Implementation idea

The classic way to check an LTL property (Vardi–Wolper's automata-theoretic approach) is to turn the problem into a **graph search for an infinite loop**, via the following pipeline:

1. **Formula → Büchi automaton.** The LTL formula is negated, converted to negation normal form, and expanded into a **generalized Büchi automaton**: an automaton over infinite words that accepts exactly the executions *violating* the property. This uses the tableau construction of Gerth, Peled, Vardi & Wolper.
2. **Simplification.** The generalized Büchi automaton (multiple accepting sets) is converted into a standard Büchi automaton (a single accepting set) via a counting/bookkeeping construction, then determinized over the relevant propositions with a powerset construction.
3. **System → Büchi automaton.** The Kripke structure is itself translated into a Büchi automaton that accepts exactly its own executions.
4. **Product.** The two automata are combined into a single **product automaton**, whose accepted words are exactly the system's executions that violate the property.
5. **Emptiness check.** The system satisfies the property **if and only if this product automaton's language is empty** — i.e. no reachable accepting cycle ("lasso") exists. This reduces to a graph search: a DFS finds candidate accepting states, then a second search looks for a cycle through one of them. If a lasso is found, it *is* a counter-example: a concrete infinite execution violating the property, which — for the puzzle — reads as a valid solution.

## Project structure

- `model_checking.ml` / `.mli` — the full pipeline: formula parsing helpers, NNF, tableau/pre-graph construction, generalized Büchi automaton, powerset & simplification to a standard Büchi automaton, Kripke-to-automaton translation, product construction, and lasso search
- `debug.ml` / `.mli` — pretty-printing helpers for formulas, automata, and solutions
- `examples.ml` / `.mli` — the wolf/goat/cabbage puzzle, encoded three different ways (see Results)
- `main.ml` — entry point, runs the model checker on a chosen formula/system pair

## Build & run

```bash
dune build
dune exec ./main.exe
```

## Results

The puzzle can be encoded in different ways: the "no one gets eaten" safety rule can live either in the **Kripke structure** (illegal states simply don't exist in the graph) or in the **LTL formula** (the property itself states "it's never the case that..."). `examples.ml` provides three such encodings, checked against the same overall goal (`F all_on_right`):

| Encoding | Where the safety rule lives | Execution time | Solution length |
|:---:|:---:|:---:|:---:|
| All in KS | Kripke structure only | 0.0001 s | 12 steps |
| Half and half | Split between KS and formula | 0.005 s | 12 steps |
| All in formula | LTL formula only | 17.4 s | 20 steps |

The three encodings are logically equivalent — they describe the same puzzle and admit a solution — but their **performance differs by five orders of magnitude**. Pushing constraints into the Kripke structure keeps the state graph small, since illegal states are simply never generated. Pushing the same constraints into the LTL formula instead makes the *formula's own automaton* far larger (more subformulas to track through the tableau construction), which blows up the product automaton the emptiness check has to search — hence the much longer runtime and the longer (less direct) solution found.

## Why this matters beyond the puzzle

The wolf/goat/cabbage puzzle is a toy example, but the technique isn't: LTL model checking is used in practice to verify hardware and safety-critical software, and — closer to robotics — to specify and verify **temporal task planning** for autonomous systems (e.g. "the robot must eventually reach the goal, and must never enter the restricted zone while carrying the payload"). This project implements that same automata-theoretic pipeline end to end, from formula to counter-example, which is the core machinery behind those applications.

## References

Gerth, R., Peled, D., Vardi, M.Y., & Wolper, P. (1995). *Simple On-the-Fly Automatic Verification of Linear Temporal Logic*. PSTV.

Vardi, M.Y., & Wolper, P. (1986). *An Automata-Theoretic Approach to Automatic Program Verification*. LICS.
