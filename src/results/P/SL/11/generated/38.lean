

theorem interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hne : A.Nonempty) : (interior A).Nonempty := by
  classical
  -- Assume, for a contradiction, that `interior A` is empty.
  by_contra hInt
  have hIntEq : interior A = (∅ : Set X) := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    have : (interior A).Nonempty := ⟨x, hx⟩
    exact (hInt this).elim
  -- Pick an element of `A`.
  rcases hne with ⟨x, hxA⟩
  -- Use `P1` to map it into the closure of the interior.
  have hxClosure : x ∈ closure (interior A) := hP1 hxA
  -- Contradiction with the fact that the interior is empty.
  have : x ∈ (∅ : Set X) := by
    simpa [hIntEq] using hxClosure
  exact (Set.not_mem_empty x) this