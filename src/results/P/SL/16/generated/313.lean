

theorem Topology.not_P2_of_nonempty_emptyInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : A.Nonempty) (hIntEmpty : interior A = (∅ : Set X)) :
    ¬ Topology.P2 (X := X) A := by
  intro hP2
  -- From `P2` and `hA`, the set `interior (closure (interior A))` is nonempty.
  have hNonempty :
      (interior (closure (interior A)) : Set X).Nonempty :=
    Topology.interior_closure_interior_nonempty_of_P2
      (X := X) (A := A) hP2 hA
  -- But `interior A = ∅`, hence its closure—and the interior of that closure—
  -- is also empty.
  have hEmpty :
      interior (closure (interior A)) = (∅ : Set X) := by
    simpa [hIntEmpty, closure_empty, interior_empty]
  -- Derive the contradiction.
  rcases hNonempty with ⟨x, hx⟩
  have : (x : X) ∈ (∅ : Set X) := by
    simpa [hEmpty] using hx
  exact this.elim