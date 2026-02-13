

theorem not_P3_of_interior_closure_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hIntClEmpty : interior (closure (A : Set X)) = (∅ : Set X)) (hne : A.Nonempty) :
    ¬ Topology.P3 A := by
  intro hP3
  -- `P3` together with non-emptiness gives a point in `interior (closure A)`.
  have hIntNonempty :=
    Topology.interior_closure_nonempty_of_P3 (A := A) hP3 hne
  rcases hIntNonempty with ⟨x, hxInt⟩
  -- This contradicts the assumption that the interior is empty.
  have : x ∈ (∅ : Set X) := by
    simpa [hIntClEmpty] using hxInt
  exact (Set.not_mem_empty x) this