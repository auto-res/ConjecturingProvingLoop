

theorem interior_inter_closure_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ closure B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClB⟩
  -- We will use the neighbourhood characterization of the closure.
  -- Reformulate the goal using `mem_closure_iff`.
  have : (∀ U : Set X, IsOpen U → x ∈ U → (U ∩ (A ∩ B)).Nonempty) := by
    intro U hU_open hxU
    -- Consider the open set `V = U ∩ interior A`, which also contains `x`.
    let V : Set X := U ∩ interior A
    have hV_open : IsOpen V := hU_open.inter isOpen_interior
    have hxV : x ∈ V := And.intro hxU hxIntA
    -- Because `x ∈ closure B`, the neighbourhood `V` meets `B`.
    have hNon : (V ∩ B).Nonempty :=
      (mem_closure_iff).1 hxClB V hV_open hxV
    -- Any point in `V ∩ B` lies in `U ∩ (A ∩ B)`.
    rcases hNon with ⟨y, hyV, hyB⟩
    have hyU : y ∈ U := hyV.1
    have hyIntA : y ∈ interior A := hyV.2
    have hyA : y ∈ A := interior_subset hyIntA
    exact ⟨y, And.intro hyU (And.intro hyA hyB)⟩
  -- Conclude that `x ∈ closure (A ∩ B)`.
  exact (mem_closure_iff).2 this