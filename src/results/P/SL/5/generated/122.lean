

theorem P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) : Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  intro x hxA
  -- Since `closure A` is open, its interior equals itself.
  have hInt : interior (closure (A : Set X)) = closure (A : Set X) :=
    hOpen.interior_eq
  -- Every point of `A` lies in `closure A`.
  have hxCl : x ∈ closure (A : Set X) := subset_closure hxA
  simpa [hInt] using hxCl