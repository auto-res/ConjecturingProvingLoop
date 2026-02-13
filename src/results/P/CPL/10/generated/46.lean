

theorem P3_subsingleton_iff {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 A ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact Topology.P3_subsingleton (X := X) (A := A)

theorem P1_union_many {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (hF : ∀ i, Topology.P1 (F i)) : Topology.P1 (⋃ i, closure (F i)) := by
  -- First, upgrade each `P1 (F i)` to `P1 (closure (F i))`.
  have hG : ∀ i, Topology.P1 (closure (F i)) := fun i =>
    Topology.P1_of_closure (hF i)
  -- Apply the `P1_iUnion` lemma to the family of closures.
  simpa using
    (Topology.P1_iUnion (F := fun i => closure (F i)) hG)