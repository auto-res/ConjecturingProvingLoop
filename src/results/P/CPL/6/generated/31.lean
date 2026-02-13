

theorem P1_iff_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact P1_closure_eq_self (A := A) hP1
  · intro hEq
    intro x hx
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hx
    simpa [hEq] using hx_cl

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (A ×ˢ B) := by
  intro hP2A hP2B
  intro x hx
  -- Decompose the hypothesis `hx : x ∈ A ×ˢ B`.
  rcases hx with ⟨hxA, hxB⟩
  -- Use the `P2` hypotheses on both coordinates.
  have hxA_int : x.1 ∈ interior (closure (interior A)) := hP2A hxA
  have hxB_int : x.2 ∈ interior (closure (interior B)) := hP2B hxB
  -- Define auxiliary neighbourhoods.
  let U : Set X := interior (closure (interior A))
  let V : Set Y := interior (closure (interior B))
  have hUopen : IsOpen U := by
    simpa [U] using isOpen_interior
  have hVopen : IsOpen V := by
    simpa [V] using isOpen_interior
  have hxU : x.1 ∈ U := by
    simpa [U] using hxA_int
  have hxV : x.2 ∈ V := by
    simpa [V] using hxB_int
  -- The open product neighbourhood around `x`.
  have hUV_open : IsOpen (U ×ˢ V) := hUopen.prod hVopen
  have hxUV   : x ∈ U ×ˢ V       := by
    exact ⟨hxU, hxV⟩
  -- Show that this neighbourhood is contained in the required closure.
  have h_subset :
      (U ×ˢ V : Set (X × Y)) ⊆ closure (interior (A ×ˢ B)) := by
    -- Step 1 : `(U ×ˢ V)` is contained in `closure (interior A) ×ˢ closure (interior B)`.
    have h1 :
        (U ×ˢ V : Set (X × Y)) ⊆
          closure (interior A) ×ˢ closure (interior B) := by
      intro y hy
      rcases hy with ⟨hyU, hyV⟩
      have hyA_cl : (y.1) ∈ closure (interior A) := by
        -- `U = interior (closure (interior A))`
        have : y.1 ∈ interior (closure (interior A)) := by
          simpa [U] using hyU
        exact interior_subset this
      have hyB_cl : (y.2) ∈ closure (interior B) := by
        have : y.2 ∈ interior (closure (interior B)) := by
          simpa [V] using hyV
        exact interior_subset this
      exact ⟨hyA_cl, hyB_cl⟩
    -- Step 2 : `closure (interior A) ×ˢ closure (interior B)`
    --         is the same as `closure ((interior A) ×ˢ (interior B))`.
    have h_prod_eq :
        (closure (interior A) ×ˢ closure (interior B) :
            Set (X × Y)) =
          closure ((interior A) ×ˢ (interior B) : Set (X × Y)) := by
      simpa using
        (closure_prod_eq (s := interior A) (t := interior B)).symm
    -- Step 3 : `interior A ×ˢ interior B ⊆ interior (A ×ˢ B)`.
    have h_int_subset :
        ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆
          interior (A ×ˢ B) := by
      intro y hy
      rcases hy with ⟨hyA, hyB⟩
      -- The open set `interior A ×ˢ interior B` is a neighbourhood of `y`
      -- contained in `A ×ˢ B`, so `y` is in the interior of `A ×ˢ B`.
      have h_open : IsOpen ((interior A) ×ˢ (interior B)) :=
        (isOpen_interior).prod isOpen_interior
      have h_nhds :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ∈ 𝓝 y :=
        h_open.mem_nhds ⟨hyA, hyB⟩
      have h_subsetAB :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ (A ×ˢ B) := by
        intro z hz; exact ⟨interior_subset hz.1, interior_subset hz.2⟩
      have h_nhds_AB : (A ×ˢ B : Set (X × Y)) ∈ 𝓝 y :=
        Filter.mem_of_superset h_nhds h_subsetAB
      exact (mem_interior_iff_mem_nhds).2 h_nhds_AB
    -- Step 4 : put everything together.
    have h2 :
        closure ((interior A) ×ˢ (interior B) : Set (X × Y))
          ⊆ closure (interior (A ×ˢ B)) :=
      closure_mono h_int_subset
    intro y hy
    have : y ∈
        closure ((interior A) ×ˢ (interior B) : Set (X × Y)) := by
      -- From `h1` and `h_prod_eq`.
      have : y ∈ closure (interior A) ×ˢ closure (interior B) := h1 hy
      simpa [h_prod_eq] using this
    exact h2 this
  -- Turn neighbourhood information into membership of the interior.
  have h_cl_nhds :
      (closure (interior (A ×ˢ B)) : Set (X × Y)) ∈ 𝓝 x :=
    Filter.mem_of_superset (hUV_open.mem_nhds hxUV) h_subset
  exact (mem_interior_iff_mem_nhds).2 h_cl_nhds

theorem P3_proj_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : P3 S → P3 (Prod.fst '' S) := by
  intro hP3S
  intro x hx
  -- Choose a point `p ∈ S` whose first coordinate is `x = p.1`.
  rcases hx with ⟨p, hpS, rfl⟩
  -- From `hP3S` we get `p ∈ interior (closure S)`.
  have hp_int : (p : X × Y) ∈ interior (closure S) := hP3S hpS
  -- View this as a neighbourhood of `p`.
  have h_int_nhds : (interior (closure S) : Set (X × Y)) ∈ 𝓝 p :=
    isOpen_interior.mem_nhds hp_int
  -- Split this product‐neighbourhood.
  rcases (mem_nhds_prod_iff).1 h_int_nhds with
    ⟨U, hU_nhds, V, hV_nhds, hUV_subset⟩
  -- `p.2` lies in `V`.
  have hpV : p.2 ∈ V := mem_of_mem_nhds hV_nhds
  -- Replace `V` by an *open* set `V' ⊆ V` still containing `p.2`.
  rcases (mem_nhds_iff.1 hV_nhds) with ⟨V', hV'subV, hV'open, hpV'⟩
  -- Show: every `z ∈ U` belongs to `closure (Prod.fst '' S)`.
  have hU_subset_closure : (U : Set X) ⊆ closure (Prod.fst '' S) := by
    intro z hzU
    -- `(z, p.2)` is in `interior (closure S)` (hence in `closure S`).
    have hz_int : (z, p.2) ∈ interior (closure S) :=
      hUV_subset ⟨hzU, hpV⟩
    have hz_cl : (z, p.2) ∈ closure S := interior_subset hz_int
    -- Use the neighbourhood characterisation of `closure`.
    have : z ∈ closure (Prod.fst '' S) := by
      refine (mem_closure_iff).2 ?_
      intro W hWopen hzW
      -- Consider the open product `W ×ˢ V'`.
      have hPopen : IsOpen (W ×ˢ V') := hWopen.prod hV'open
      have hzP : (z, p.2) ∈ W ×ˢ V' := by
        exact ⟨hzW, hpV'⟩
      -- `S` meets this open neighbourhood.
      have h_nonempty : ((W ×ˢ V') ∩ S).Nonempty :=
        (mem_closure_iff).1 hz_cl _ hPopen hzP
      rcases h_nonempty with ⟨r, ⟨hrP, hrS⟩⟩
      rcases hrP with ⟨hrW, _hrV⟩
      exact ⟨r.1, ⟨hrW, ⟨r, hrS, rfl⟩⟩⟩
    exact this
  -- Hence `closure (Prod.fst '' S)` is a neighbourhood of `p.1`.
  have h_closure_nhds : (closure (Prod.fst '' S) : Set X) ∈ 𝓝 p.1 :=
    Filter.mem_of_superset hU_nhds hU_subset_closure
  -- Conclude `p.1 ∈ interior (closure (Prod.fst '' S))`.
  exact (mem_interior_iff_mem_nhds).2 h_closure_nhds

theorem P3_bot {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; intro x hx; cases hx

theorem P2_top {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact P2_univ (X := X)