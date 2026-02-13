

theorem P1_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P1 (Aᶜ) := by
  intro hA_closed
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ : Set X) := (isOpen_compl_iff).2 hA_closed
  -- Hence its interior is itself.
  have hInt : interior (Aᶜ : Set X) = (Aᶜ : Set X) := hOpen.interior_eq
  -- Now prove the required inclusion.
  intro x hx
  -- Any point of `Aᶜ` is in its closure.
  have hx_closure : x ∈ closure (Aᶜ : Set X) := subset_closure hx
  -- Re-express using `hInt`.
  simpa [hInt] using hx_closure

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (Set.prod A B) := by
  intro hP2A hP2B
  intro p hp
  -- Split the point into its two coordinates.
  rcases hp with ⟨hpA, hpB⟩
  -- Each coordinate satisfies the `P2` condition.
  have hA : p.1 ∈ interior (closure (interior A)) := hP2A hpA
  have hB : p.2 ∈ interior (closure (interior B)) := hP2B hpB
  ------------------------------------------------------------------
  -- An explicit open neighbourhood of `p`.
  ------------------------------------------------------------------
  set U : Set X := interior (closure (interior A)) with hU
  set V : Set Y := interior (closure (interior B)) with hV
  have hU_open  : IsOpen U := by
    simpa [hU] using isOpen_interior
  have hV_open  : IsOpen V := by
    simpa [hV] using isOpen_interior
  have hUV_open : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have hpUV : p ∈ U ×ˢ V := by
    have hpU : p.1 ∈ U := by
      simpa [hU] using hA
    have hpV : p.2 ∈ V := by
      simpa [hV] using hB
    exact ⟨hpU, hpV⟩
  ------------------------------------------------------------------
  -- `U ×ˢ V` is contained in the closure of `interior (A ×ˢ B)`.
  ------------------------------------------------------------------
  have h_sub :
      (U ×ˢ V) ⊆ closure (interior (Set.prod A B)) := by
    intro q hq
    rcases hq with ⟨hqU, hqV⟩
    -- Rewrite the memberships.
    have hq1 : q.1 ∈ interior (closure (interior A)) := by
      simpa [hU] using hqU
    have hq2 : q.2 ∈ interior (closure (interior B)) := by
      simpa [hV] using hqV
    -- Pass to the closures of the interiors of the factors.
    have hq1_cl : q.1 ∈ closure (interior A) := interior_subset hq1
    have hq2_cl : q.2 ∈ closure (interior B) := interior_subset hq2
    -- Hence `q` lies in the product of these two closures.
    have hq_prod : q ∈
        (closure (interior A)) ×ˢ (closure (interior B)) :=
      ⟨hq1_cl, hq2_cl⟩
    -- Identify this product with the closure of the product
    -- of the two interiors.
    have h_cl_eq :
        closure ((interior A) ×ˢ (interior B)) =
          (closure (interior A)) ×ˢ (closure (interior B)) := by
      simpa using closure_prod_eq
    have hq_in_cl_prod :
        q ∈ closure ((interior A) ×ˢ (interior B)) := by
      simpa [h_cl_eq] using hq_prod
    -- The product of interiors is contained in the interior
    -- of the product.
    have h_small :
        ((interior A) ×ˢ (interior B)) ⊆ interior (Set.prod A B) := by
      apply interior_maximal
      · intro z hz
        rcases hz with ⟨hz1, hz2⟩
        exact ⟨interior_subset hz1, interior_subset hz2⟩
      · exact (isOpen_interior.prod isOpen_interior)
    -- Taking closures preserves inclusions.
    have h_cl_small :
        closure ((interior A) ×ˢ (interior B)) ⊆
          closure (interior (Set.prod A B)) :=
      closure_mono h_small
    exact h_cl_small hq_in_cl_prod
  ------------------------------------------------------------------
  -- `U ×ˢ V` is an open subset of the required closure, hence
  -- contained in its interior.
  ------------------------------------------------------------------
  have h_into :
      (U ×ˢ V) ⊆ interior (closure (interior (Set.prod A B))) :=
    interior_maximal h_sub hUV_open
  exact h_into hpUV

theorem P1_equiv_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P1 (e '' A) → P1 A := by
  intro hP1_image
  -- Transport the `P1` property along the inverse homeomorphism.
  have hP1_preimage : P1 (e.symm '' (e '' A)) :=
    P1_image_homeomorph (e := e.symm) (A := e '' A) hP1_image
  -- Identify `e.symm '' (e '' A)` with `A`.
  have h_eq : (e.symm '' (e '' A) : Set X) = A := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      rcases hy with ⟨z, hzA, rfl⟩
      -- `hxy` is `e.symm (e z) = x`.
      have : z = x := by
        simpa [e.symm_apply_apply] using hxy
      simpa [this] using hzA
    · intro hxA
      refine ⟨e x, ?_, ?_⟩
      · exact ⟨x, hxA, rfl⟩
      · simp
  -- Prove the desired `P1` statement for `A`.
  intro x hxA
  -- `x` lies in `e.symm '' (e '' A)`.
  have hx_pre : x ∈ e.symm '' (e '' A) := by
    refine ⟨e x, ?_, ?_⟩
    · exact ⟨x, hxA, rfl⟩
    · simp
  -- Apply the transported `P1` property.
  have hx_cl : x ∈ closure (interior (e.symm '' (e '' A))) :=
    hP1_preimage hx_pre
  -- Reinterpret the result using the set equality obtained above.
  simpa [h_eq] using hx_cl