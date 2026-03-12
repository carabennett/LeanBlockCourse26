import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-
## Handshaking lemma: the sum of the degrees in a graph is twice the number of its edges

A *simple graph* `G = (V, E)` is defined by its set of *vertices (nodes)* `V` and
a set of *edges* `∅ ⊆ E ⊆ { e = {u, v} ∣ u ≠ v ∈ V }`. It is *finite* if `V` is
finite and its *order* denotes `#V` and *size* denotes `#E`.

The edges can also be interpreted as a relationship `~` between vertices,
where `u ~ v` if and only if `{u, v} ∈ E` (which in particular implies that
`u ≠ v`). Two vertices defining an edge are said to be *adjacent* and an edge
and any of its two vertices are said to be *incident*.

The *neighborhood* of a vertex `v` is defined as `N(v) = {u | u ~ v}`. Its
*degree* `d(v) = #N(v)` is simply the cardinality of its neighborhood.
The *incidence set* of a vertex `v` is defined as `I(v) = {e ∈ E | v ∈ e}`.

**Handshake Lemma.** Given any finite simple graph `G = (V, E)`, the sum of the
degrees of all its vertices equals twice its size, that is `Σ_v d(v) = 2 * #E`.
-/

/-
# Phase 1: Find out as much as is useful about simple graphs in `mathlib`

The two most relevant files / import should probably be
`Mathlib.Combinatorics.SimpleGraph.Basic` There we find
the definition of a simple graph `G` ...

```
structure SimpleGraph (V : Type u) where
  Adj : V → V → Prop
  symm : Symmetric Adj       := by aesop_graph
  loopless : Std.Irrefl Adj  := by aesop_graph
```

... and that we can get the edge set through `G.edgeSet`.
We can also find the definition of an incidence set ...

```
def incidenceSet (v : V) : Set (Sym2 V) :=
  { e ∈ G.edgeSet | v ∈ e }
```

... and the neighborhood set ...

```
def neighborSet (v : V) : Set V := {w | G.Adj v w}
```

... but you will not fine a notion of degree. Why? Because
this requires your graph to be finite. Luckily, we have
`Mathlib.Combinatorics.SimpleGraph.Finite`, which states

> The design for finiteness is that each definition takes
> the smallest finiteness assumption necessary. For example,
> `SimpleGraph.neighborFinset v` only requires that `v` have
> finitely many neighbors.

Working backwards, we first see that the degree is

```
def degree : ℕ := #(G.neighborFinset v)
```

... with ...

```
def neighborFinset : Finset V := (G.neighborSet v).toFinset
```

... where we recall that we have already seen `Set.toFinset`
in P06S01. Both of these get their finiteness by assuming
`Fintype ↑(G.neighborSet v)`. For us, we will need this to
hold for each `v`, so the better type class assumption to
use should be `[Fintype V]`. This also gives us access to

```
def edgeFinset : Finset (Sym2 V) := Set.toFinset G.edgeSet
```

There will (probably) be more importants needed once we 
understand the actual proof, but from the theorem statement
we can already infer that we might need `Finset.sum` and the
theorems about it from `Mathlib.Algebra.Order.BigOperators.Ring.Finset`
-/

/-
# Phase 2: Write down the statement of the handshake lemma in lean with `sorry`
-/

-- The arguments of your theorem should probably look like this ...
variable {V : Type*} (G : SimpleGraph V)

-- ... with the following finiteness and decidability assumptions giving you ...
variable [Fintype V] [DecidableRel G.Adj]

/-
A first attempt after stating `[Fintype V]` and noting that both `G.edgeFinset`
and `G.degree v` complain, might have been to also require `[Fintype G.edgeSet]`
and some assumption about the neighborhood of each vertex being finite ...

... but the actual issue is that we need to assure lean that our graph adjacency
notion is decidable (two vertices are either adjacent), leading to 
`[DecidableEq V]`. Note that his does not already invoke classical axioms
(excluded middle) because when "using" the lemma for a specific explicitly
constructed graph, you can supply you constructive proof of decidability
for that particular graph. But you can also invoke `Classical.choice` for any
arbitrary graph, making the lemma generally valid in classical logic.
-/ 

-- ... access to sums over `Fintype`s or `Finset`s so we can state ...
lemma handshaking : ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  sorry

/-
What we should *not* try to do is to define a finite vertex set `V` and
use that as the argument of the `SimpleGraph`, even though lean is able 
to coerce it into the type `{v : α // v ∈ V}`.

```
example {α : Type*} (V : Set α) (h : V.Finite) (G : SimpleGraph V) : False := by ...
```
-/

/-
# Phase 3: Find a proof of the handshake lemma that you like and flesh it out

According to [Wikipedia](https://en.wikipedia.org/wiki/Handshaking_lemma)

> Euler's proof of the degree sum formula uses the technique of *double counting*:
> he counts the number of incident pairs `(v, e)` where `e` is an edge and vertex 
> `v` is one of its endpoints, in two different ways. Vertex `v` belongs to 
> `deg(v)` pairs, where the degree of `v` is the number of edges incident to it.
> Therefore, the number of incident pairs is the sum of the degrees. However,
> each edge in the graph belongs to exactly two incident pairs, one for each of
> its endpoints; therefore, the number of incident pairs is  `2|E|`. Since
> these two formulas count the same set of objects, they must have equal values.

The main ingredients are:

1. **Double counting** given two finite sets `A` and `B` and a relationship `R`
   between them denoted by `R a b`, we can count the number of pairs `(a, b)` for
   which `R a b` both over `A` and over `B`: 
  
   ```
   ∑ a ∈ A, #{b ∈ B | R a b} = ∑ b ∈ B, #{a ∈ A | R a b}.
   ``` 

2. We count "the number of incident pairs `(v, e)` where `e` is an edge and vertex 
   `v` is one of its endpoints", so for our application of double counting
   `A = V`, `B = E` and `R a b = a ∈ b`, giving us 
    
   ```
   ∑ v, #{ e ∈ E | v ∈ e } = ∑ a ∈ A, #{b ∈ B | R a b}
                           = ∑ b ∈ B, #{a ∈ A | R a b}
                           = ∑ e ∈ E, #{ v ∈ V | v ∈ e}
   ```

3. We need to show that `G.degree v = #{ e ∈ E | v ∈ e }` for any `v ∈ V`.

4. We need to show that `2 * G.edgeFinset.card = ∑ e ∈ E, #{ v ∈ V | v ∈ e }`.

5. And then simply chain 3, 4, and 2 together to get the desired statement.
-/

/-
# Phase 4: Find out as much as is useful for your proof in `mathlib`

1. Find the double counting argument in mathlib! It should be some statement
   taking exactly `A : Type*`, `B : Type*`, and `R : A → B → Prop` as an input.

2. Find `∑ s ∈ S, C = C * #S` for any finite set `S` and constant `C`.

3. Find `#{ v ∈ V | v ∈ e } = 2` for any graph `G` and one if its edges `e`.

4. Find `G.degree v = #{ e ∈ E | v ∈ e }` for any graph `G` and one if its vertices `v`.
-/

/-
# Phase 5: Implement your fleshed out proof as closely as possible in lean
-/
