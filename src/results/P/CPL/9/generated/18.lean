

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 (A := A)) (hB : Topology.P3 (A := B)) : Topology.P3 (A := Set.prod A B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- use `P3` on the two coordinates
  have hx : p.fst ∈ interior (closure A) := hA hpA
  have hy : p.snd ∈ interior (closure B) := hB hpB
  -- auxiliary open neighbourhoods
  set U : Set X := interior (closure A) with hU_def
  set V : Set Y := interior (closure B) with hV_def
  have hU_open : IsOpen U := by
    simpa [hU_def] using isOpen_interior
  have hV_open : IsOpen V := by
    simpa [hV_def] using isOpen_interior
  have hpU : p.fst ∈ U := by
    simpa [hU_def] using hx
  have hpV : p.snd ∈ V := by
    simpa [hV_def] using hy
  have hpUV : p ∈ Set.prod U V := by
    exact ⟨hpU, hpV⟩
  -- inclusion towards the target closure
  have hU_subset : (U : Set X) ⊆ closure A := by
    intro x hx
    simpa [hU_def] using (interior_subset hx)
  have hV_subset : (V : Set Y) ⊆ closure B := by
    intro y hy
    simpa [hV_def] using (interior_subset hy)
  have hUV_subset_prodCl :
      Set.prod U V ⊆ Set.prod (closure A) (closure B) :=
    Set.prod_mono hU_subset hV_subset
  have h_prod_eq :
      closure (Set.prod A B) = Set.prod (closure A) (closure B) := by
    simpa using (closure_prod_eq :
      closure (Set.prod A B) = Set.prod (closure A) (closure B))
  have hUV_subset :
      Set.prod U V ⊆ closure (Set.prod A B) := by
    intro q hq
    have hq' : q ∈ Set.prod (closure A) (closure B) :=
      hUV_subset_prodCl hq
    simpa [h_prod_eq] using hq'
  -- `U × V` is an open neighbourhood of `p`
  have h_openUV : IsOpen (Set.prod U V) :=
    hU_open.prod hV_open
  have hUV_nhds : Set.prod U V ∈ 𝓝 p :=
    h_openUV.mem_nhds hpUV
  -- upgrade the neighbourhood using the inclusion
  have h_target_nhds :
      closure (Set.prod A B) ∈ 𝓝 p :=
    Filter.mem_of_superset hUV_nhds hUV_subset
  -- conclude
  exact (mem_interior_iff_mem_nhds).2 h_target_nhds

theorem P3_closed_iff_self {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 (A := A) ↔ A = interior (closure A) := by
  -- Since `A` is closed we have `closure A = A`.
  have h_closure : closure A = A := hA.closure_eq
  -- Hence `interior (closure A)` is contained in `A`.
  have h_int_subset : interior (closure A) ⊆ A := by
    intro x hx
    -- `x ∈ closure A`
    have h_mem : (x : X) ∈ closure A := interior_subset hx
    -- Rewrite using `h_closure`.
    have h_memA : x ∈ A := by
      have h_tmp := h_mem
      rw [h_closure] at h_tmp
      exact h_tmp
    exact h_memA
  -- Establish the equivalence.
  constructor
  · -- `P3 A → A = interior (closure A)`
    intro hP3
    exact Set.Subset.antisymm hP3 h_int_subset
  · -- `A = interior (closure A) → P3 A`
    intro h_eq
    intro x hx
    -- Rewrite the assumption using the given equality.
    have hx' : x ∈ interior (closure A) := by
      have h_tmp := hx
      rw [h_eq] at h_tmp
      exact h_tmp
    exact hx'

theorem P2_unionᵢ {X : Type*} [TopologicalSpace X] {ι κ} (s : ι → κ → Set X) (h : ∀ i j, Topology.P2 (A := s i j)) : Topology.P2 (A := ⋃ i, ⋃ j, s i j) := by
  -- For each fixed `i`, the union over `j` satisfies `P2`.
  have h₁ : ∀ i, Topology.P2 (A := ⋃ j, s i j) := by
    intro i
    have hi : Topology.P2 (A := ⋃ j, s i j) :=
      P2_iUnion (s := s i) (h := fun j => h i j)
    simpa using hi
  -- Now take the union over `i`.
  have h₂ : Topology.P2 (A := ⋃ i, ⋃ j, s i j) :=
    P2_iUnion (s := fun i => ⋃ j, s i j) (h := h₁)
  simpa using h₂

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P1 (A := A)) : Topology.P1 (A := e '' A) := by
  -- We have to show: `e '' A ⊆ closure (interior (e '' A))`.
  intro y hy
  -- Obtain a preimage point `x`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- From `P1` for `A`, we know `x ∈ closure (interior A)`.
  have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
  -- Send this fact through the homeomorphism.
  have hx_img_cl : (e x : Y) ∈ closure (e '' interior A) := by
    -- First note `e x ∈ e '' closure (interior A)`.
    have h_mem : (e x : Y) ∈ e '' closure (interior A) := ⟨x, hx_cl, rfl⟩
    -- Identify this set with `closure (e '' interior A)`.
    have h_eq : (e '' closure (interior A) : Set Y) = closure (e '' interior A) := by
      simpa using e.image_closure (s := interior A)
    simpa [h_eq] using h_mem
  -- Enlarge the closure once more.
  have h_subset : (closure (e '' interior A) : Set Y) ⊆
      closure (interior (e '' A)) := by
    -- First, `e '' interior A ⊆ interior (e '' A)`.
    have h_sub : (e '' interior A : Set Y) ⊆ interior (e '' A) := by
      intro z hz
      -- Rewrite using `image_interior`.
      have h_eq_int : (e '' interior A : Set Y) = interior (e '' A) := by
        simpa using e.image_interior (s := A)
      simpa [h_eq_int] using hz
    -- Take closures.
    exact closure_mono h_sub
  -- Apply the inclusion.
  exact h_subset hx_img_cl

theorem exists_P1_subset_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 (A := A)) : ∃ U, IsOpen U ∧ A ⊆ U ∧ Topology.P1 (A := U) := by
  refine ⟨Set.univ, isOpen_univ, ?_, P1_univ (X := X)⟩
  exact Set.subset_univ _