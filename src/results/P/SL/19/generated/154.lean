

theorem Topology.interior_union_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  -- First, move `x` into `interior (A ∪ B)` using an existing lemma.
  have hxUnion : x ∈ interior (A ∪ B) :=
    (Topology.interior_union (X := X) (A := A) (B := B)) hx
  -- Since `A ∪ B ⊆ closure (A ∪ B)`, monotonicity of `interior` upgrades the membership.
  have hSub : (A ∪ B : Set X) ⊆ closure (A ∪ B) := subset_closure
  exact (interior_mono hSub) hxUnion