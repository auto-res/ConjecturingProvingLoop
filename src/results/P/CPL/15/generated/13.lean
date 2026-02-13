

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (A ×ˢ B) := by
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- points are in the `P2` interiors
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  have hy_int : y ∈ interior (closure (interior B)) := hB hyB
  -- choose open neighbourhoods
  rcases mem_interior.1 hx_int with ⟨U, hU_sub, hU_open, hxU⟩
  rcases mem_interior.1 hy_int with ⟨V, hV_sub, hV_open, hyV⟩
  -- open neighbourhood in the product
  have hUV_open : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have hpUV : ((x, y) : X × Y) ∈ U ×ˢ V := And.intro hxU hyV
  -- show the neighbourhood is contained in the required set
  have hUV_sub : (U ×ˢ V : Set (X × Y)) ⊆ closure (interior (A ×ˢ B)) := by
    intro z hz
    -- first, place `z` in the product of closures
    have hz_prod : z ∈ closure (interior A) ×ˢ closure (interior B) :=
      (Set.prod_mono hU_sub hV_sub) hz
    -- rewrite via `closure_prod_eq`
    have hz_cl₁ : z ∈ closure (interior A ×ˢ interior B) := by
      simpa [closure_prod_eq] using hz_prod
    -- `interior A × interior B` is an open subset of `A × B`
    have h_inner_subset :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
      intro w hw
      have h_open : IsOpen (interior A ×ˢ interior B) :=
        isOpen_interior.prod isOpen_interior
      have h_sub : (interior A ×ˢ interior B : Set (X × Y)) ⊆ A ×ˢ B :=
        Set.prod_mono interior_subset interior_subset
      exact mem_interior.2 ⟨_, h_sub, h_open, hw⟩
    have h_closure_subset :
        (closure (interior A ×ˢ interior B) : Set (X × Y)) ⊆
          closure (interior (A ×ˢ B)) :=
      closure_mono h_inner_subset
    exact h_closure_subset hz_cl₁
  -- conclude
  exact mem_interior.2 ⟨U ×ˢ V, hUV_sub, hUV_open, hpUV⟩