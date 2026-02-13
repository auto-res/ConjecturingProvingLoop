

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (Set.prod A B) := by
  intro hP2A hP2B
  intro p hpProd
  rcases hpProd with ⟨hpA, hpB⟩
  -- Auxiliary open sets in the two coordinates.
  set SA := interior (closure (interior A)) with hSAdef
  set SB := interior (closure (interior B)) with hSBdef
  have hSA : p.1 ∈ SA := by
    have : p.1 ∈ interior (closure (interior A)) := hP2A hpA
    simpa [hSAdef] using this
  have hSB : p.2 ∈ SB := by
    have : p.2 ∈ interior (closure (interior B)) := hP2B hpB
    simpa [hSBdef] using this
  -- An open neighbourhood of `p` in the product space.
  let O : Set (X × Y) := Set.prod SA SB
  have hOopen : IsOpen O := by
    have hSAopen : IsOpen SA := by
      have : IsOpen (interior (closure (interior A))) := isOpen_interior
      simpa [hSAdef] using this
    have hSBopen : IsOpen SB := by
      have : IsOpen (interior (closure (interior B))) := isOpen_interior
      simpa [hSBdef] using this
    simpa [O] using hSAopen.prod hSBopen
  have hpO : p ∈ O := by
    dsimp [O]; exact ⟨hSA, hSB⟩
  -- Show that this neighbourhood is contained in the desired set.
  have hO_sub : O ⊆ closure (interior (Set.prod A B)) := by
    intro q hqO
    dsimp [O] at hqO
    rcases hqO with ⟨hqSA, hqSB⟩
    have hqClA : q.1 ∈ closure (interior A) := interior_subset hqSA
    have hqClB : q.2 ∈ closure (interior B) := interior_subset hqSB
    have hqProdCl :
        q ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
      ⟨hqClA, hqClB⟩
    -- `closure (interior A × interior B)` equals this product.
    have h_cl_eq :
        closure (Set.prod (interior A) (interior B)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using closure_prod_eq (s := interior A) (t := interior B)
    have hq_in_closure_prod :
        q ∈ closure (Set.prod (interior A) (interior B)) := by
      simpa [h_cl_eq] using hqProdCl
    -- Relate the two closures via monotonicity.
    have h_subset :
        closure (Set.prod (interior A) (interior B)) ⊆
          closure (interior (Set.prod A B)) := by
      -- First, `interior A × interior B` lies in `interior (A × B)`.
      have h_sub :
          Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
        have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
          (isOpen_interior.prod isOpen_interior)
        have h_sub' :
            Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
          intro r hr
          rcases hr with ⟨hrA, hrB⟩
          exact ⟨interior_subset hrA, interior_subset hrB⟩
        exact interior_maximal h_sub' h_open
      exact closure_mono h_sub
    exact h_subset hq_in_closure_prod
  -- Use `O` to witness that `p` is in the required interior.
  have h_nhds : O ∈ 𝓝 p := hOopen.mem_nhds hpO
  have h_mem :
      p ∈ interior (closure (interior (Set.prod A B))) :=
    (mem_interior_iff_mem_nhds).2 (Filter.mem_of_superset h_nhds hO_sub)
  simpa [O, hSAdef, hSBdef] using h_mem