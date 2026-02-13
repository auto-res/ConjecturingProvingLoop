

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ×ˢ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA hB ⊢
  intro p hp
  -- Apply the `P2` property to both coordinates of `p`.
  have hpA : p.1 ∈ interior (closure (interior A)) := hA hp.1
  have hpB : p.2 ∈ interior (closure (interior B)) := hB hp.2
  -- The product of these interiors is an open neighbourhood of `p`.
  have hOpen :
      IsOpen (Set.prod (interior (closure (interior A)))
                       (interior (closure (interior B)))) := by
    have h1 : IsOpen (interior (closure (interior A))) := isOpen_interior
    have h2 : IsOpen (interior (closure (interior B))) := isOpen_interior
    exact h1.prod h2
  have hMem :
      (p : X × Y) ∈
        Set.prod (interior (closure (interior A)))
                 (interior (closure (interior B))) := by
    exact ⟨hpA, hpB⟩
  -- Show that this neighbourhood is contained in `closure (interior (A ×ˢ B))`.
  have hSubset :
      Set.prod (interior (closure (interior A)))
               (interior (closure (interior B))) ⊆
        closure (interior (A ×ˢ B)) := by
    intro q hq
    rcases hq with ⟨hqA, hqB⟩
    -- Each coordinate lies in the corresponding closure.
    have hqA_cl : q.1 ∈ closure (interior A) := interior_subset hqA
    have hqB_cl : q.2 ∈ closure (interior B) := interior_subset hqB
    have hProdMem :
        (q : X × Y) ∈ closure (interior A) ×ˢ closure (interior B) :=
      ⟨hqA_cl, hqB_cl⟩
    -- Relate product closures to the closure of a product.
    have h_closure_prod :
        closure ((interior A) ×ˢ (interior B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      simpa using closure_prod_eq (s := interior A) (t := interior B)
    have hq_mem_closure_prod :
        (q : X × Y) ∈ closure ((interior A) ×ˢ (interior B)) := by
      simpa [h_closure_prod] using hProdMem
    -- Identify `interior (A ×ˢ B)`.
    have h_int_prod :
        interior (A ×ˢ B) = (interior A) ×ˢ (interior B) := by
      simpa using interior_prod_eq (s := A) (t := B)
    simpa [h_int_prod] using hq_mem_closure_prod
  -- Turn the neighbourhood inclusion into an interior membership.
  have hNhds :
      closure (interior (A ×ˢ B)) ∈ 𝓝 p :=
    Filter.mem_of_superset (hOpen.mem_nhds hMem) hSubset
  exact (mem_interior_iff_mem_nhds).2 hNhds