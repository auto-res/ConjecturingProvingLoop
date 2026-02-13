

theorem nonempty_interior_of_nonempty_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X)) (hNon : (A : Set X).Nonempty) :
    (interior (A : Set X)).Nonempty := by
  classical
  by_contra hInt
  -- From `¬ (interior A).Nonempty`, deduce `interior A = ∅`.
  have hIntEmpty : interior (A : Set X) = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hInt
  -- Hence its closure is also empty.
  have hClosureEmpty : closure (interior (A : Set X)) = (∅ : Set X) := by
    simpa [hIntEmpty, closure_empty] using rfl
  -- Pick an element of `A` (it exists by `hNon`).
  rcases hNon with ⟨x, hxA⟩
  -- `P1` puts this element inside the (empty) closure, contradiction.
  have : x ∈ closure (interior (A : Set X)) := hP1 hxA
  simpa [hClosureEmpty] using this