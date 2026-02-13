

theorem P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 (closure A)) : P3 A := by
  intro x hxA
  -- `x` lies in the closure of `A`.
  have hx_cl : (x : X) ∈ closure A := subset_closure hxA
  -- Apply `P2` for `closure A`.
  have hx_int :
      x ∈ interior (closure (interior (closure A))) := h hx_cl
  -- Show the interior set above is contained in `interior (closure A)`.
  have h_subset :
      (interior (closure (interior (closure A))) : Set X) ⊆
        interior (closure A) := by
    -- First, prove an inclusion for the closures.
    have h_closure_sub :
        (closure (interior (closure A)) : Set X) ⊆ closure A := by
      -- Since `interior (closure A) ⊆ closure A`, take closures.
      have h' : (interior (closure A) : Set X) ⊆ closure A :=
        interior_subset
      have h'' :
          (closure (interior (closure A)) : Set X) ⊆
            closure (closure A) :=
        closure_mono h'
      simpa [closure_closure] using h''
    -- Pass to interiors.
    exact interior_mono h_closure_sub
  -- Conclude the desired membership.
  exact h_subset hx_int

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (Set.prod A (Set.prod B C)) := by
  -- First derive `P2` for the product `B × C`.
  have hBC : P2 (Set.prod B C) := P2_prod (A := B) (B := C) hB hC
  -- Then apply `P2_prod` once more to get the desired result.
  exact P2_prod (A := A) (B := Set.prod B C) hA hBC