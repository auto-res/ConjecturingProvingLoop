

theorem Topology.P3_inter_isOpen_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hOpenA : IsOpen A) (hP3B : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- Expand the definition of `P3`.
  unfold Topology.P3 at *
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P3` for `B`, we get that `x` lies in the interior of `closure B`.
  have hxIntB : x ∈ interior (closure B) := hP3B hxB
  -- The point `x` lies in the open set `A ∩ interior (closure B)`.
  have hxS : x ∈ A ∩ interior (closure B) := And.intro hxA hxIntB
  -- We will show that this open set is contained in `closure (A ∩ B)`.
  have h_subset : (A ∩ interior (closure B)) ⊆ closure (A ∩ B) := by
    intro y hy
    rcases hy with ⟨hyA, hyIntB⟩
    -- `y` belongs to `closure B`.
    have hyClB : y ∈ closure B := interior_subset hyIntB
    -- Prove that `y` is in `closure (A ∩ B)` using the neighbourhood
    -- characterization of the closure.
    have : y ∈ closure (A ∩ B) := by
      apply (mem_closure_iff).2
      intro U hU_open hyU
      -- Refine the neighbourhood to stay inside `A`, which is open.
      have hUA_open : IsOpen (U ∩ A) := hU_open.inter hOpenA
      have hyUA : y ∈ U ∩ A := ⟨hyU, hyA⟩
      -- Because `y ∈ closure B`, the set `(U ∩ A)` meets `B`.
      have h_nonempty : ((U ∩ A) ∩ B).Nonempty := by
        have h := (mem_closure_iff).1 hyClB (U ∩ A) hUA_open hyUA
        simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h
      -- Extract a witness in the required intersection.
      rcases h_nonempty with ⟨z, ⟨⟨hzU, hzA⟩, hzB⟩⟩
      exact ⟨z, And.intro hzU (And.intro hzA hzB)⟩
    exact this
  -- The set `A ∩ interior (closure B)` is open.
  have h_open : IsOpen (A ∩ interior (closure B)) :=
    hOpenA.inter isOpen_interior
  -- Use `interior_maximal` to deduce an inclusion into the interior.
  have h_interior :
      (A ∩ interior (closure B)) ⊆ interior (closure (A ∩ B)) :=
    interior_maximal h_subset h_open
  -- Conclude for the original point `x`.
  exact h_interior hxS