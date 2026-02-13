

theorem P3_of_dense_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (closure (interior A))) : Topology.P3 (A := A) := by
  intro x hx
  -- Step 1: `closure (interior A)` is dense, hence equals `univ`.
  have h_dense_eq : (closure (interior A) : Set X) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Step 2: deduce `closure A = univ`.
  have h_closureA_univ : (closure A : Set X) = (Set.univ : Set X) := by
    -- `closure (interior A)` is contained in `closure A`.
    have h_subset : closure (interior A) ⊆ closure A := by
      apply closure_mono
      exact interior_subset
    -- So `univ` is contained in `closure A`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      intro y hy
      have : (y : X) ∈ closure (interior A) := by
        -- rewrite using `h_dense_eq`
        simpa [h_dense_eq] using hy
      exact h_subset this
    exact Set.Subset.antisymm (Set.subset_univ _) h_univ_subset
  -- Step 3: therefore `interior (closure A) = univ`.
  have h_int_eq : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closureA_univ, interior_univ]
  -- Step 4: conclude the desired membership.
  simpa [h_int_eq]

theorem P2_product {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) : Topology.P2 (A := Set.prod A B) := by
  intro p hp
  -- Split the membership of the point `p : X × Y`
  rcases hp with ⟨hpA, hpB⟩
  -- Use the `P2` hypotheses on the two coordinates
  have hx : p.fst ∈ interior (closure (interior A)) := hA hpA
  have hy : p.snd ∈ interior (closure (interior B)) := hB hpB
  -- Define convenient open neighbourhoods of the two coordinates
  set U : Set X := interior (closure (interior A)) with hU_def
  set V : Set Y := interior (closure (interior B)) with hV_def
  have hU_open : IsOpen U := by
    simpa [hU_def] using isOpen_interior
  have hV_open : IsOpen V := by
    simpa [hV_def] using isOpen_interior
  have hpU : p.fst ∈ U := by
    simpa [hU_def] using hx
  have hpV : p.snd ∈ V := by
    simpa [hV_def] using hy
  -- The open rectangle around `p`
  have hpUV : p ∈ Set.prod U V := by
    exact ⟨hpU, hpV⟩
  -- `U × V ⊆ (closure (interior A)) × (closure (interior B))`
  have hU_subset : (U : Set X) ⊆ closure (interior A) := by
    intro x hx
    simpa [hU_def] using (interior_subset hx)
  have hV_subset : (V : Set Y) ⊆ closure (interior B) := by
    intro y hy
    simpa [hV_def] using (interior_subset hy)
  have hUV_subset_prodCl :
      Set.prod U V ⊆
        Set.prod (closure (interior A)) (closure (interior B)) :=
    Set.prod_mono hU_subset hV_subset
  -- Identify the product of closures with the closure of the product
  have h_prod_eq :
      closure (Set.prod (interior A) (interior B)) =
        Set.prod (closure (interior A)) (closure (interior B)) := by
    simpa using closure_prod_eq
  have hUV_subset :
      Set.prod U V ⊆ closure (Set.prod (interior A) (interior B)) := by
    simpa [h_prod_eq] using hUV_subset_prodCl
  -- `interior A × interior B ⊆ interior (A × B)`
  have h_prod_int_subset :
      Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
    have h_subset :
        Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
      intro q hq
      rcases hq with ⟨h1, h2⟩
      exact ⟨interior_subset h1, interior_subset h2⟩
    have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
      (isOpen_interior.prod isOpen_interior)
    exact interior_maximal h_subset h_open
  -- Enlarge once more to reach the desired closure
  have h_closure_mono :
      closure (Set.prod (interior A) (interior B)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_prod_int_subset
  have hUV_subset_target :
      Set.prod U V ⊆ closure (interior (Set.prod A B)) :=
    Set.Subset.trans hUV_subset h_closure_mono
  -- `U × V` is an open neighbourhood of `p`
  have h_openUV : IsOpen (Set.prod U V) :=
    hU_open.prod hV_open
  have hUV_nhds : Set.prod U V ∈ 𝓝 p :=
    h_openUV.mem_nhds hpUV
  -- Upgrade the neighbourhood using the inclusion
  have h_target_nhds :
      closure (interior (Set.prod A B)) ∈ 𝓝 p :=
    Filter.mem_of_superset hUV_nhds hUV_subset_target
  -- Conclude that `p` lies in the required interior
  have hp_int :
      p ∈ interior (closure (interior (Set.prod A B))) :=
    (mem_interior_iff_mem_nhds).2 h_target_nhds
  exact hp_int