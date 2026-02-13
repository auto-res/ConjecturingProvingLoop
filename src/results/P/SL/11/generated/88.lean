

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3] at *
  intro x hxA
  -- Since `x ∈ A`, we have `x ∈ closure A`.
  have hxCl : x ∈ closure A := subset_closure hxA
  -- Because `closure A` is open, its interior is itself.
  have hIntEq : interior (closure A) = closure A := hOpenCl.interior_eq
  -- Conclude that `x` lies in the required interior.
  simpa [hIntEq] using hxCl