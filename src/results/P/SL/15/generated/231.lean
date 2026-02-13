

theorem closure_prod_nonempty_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    (closure (A ×ˢ B)).Nonempty ↔
      ((closure (A : Set X)).Nonempty ∧ (closure (B : Set Y)).Nonempty) := by
  -- Express the closure of the product as a product of closures.
  have hEq :
      closure (A ×ˢ B) =
        (closure (A : Set X)) ×ˢ (closure (B : Set Y)) := by
    simpa using closure_prod_eq (s := A) (t := B)
  constructor
  · -- `→` direction
    intro hProd
    rcases hProd with ⟨p, hp⟩
    -- Transport the membership through `hEq`.
    have hp' : (p : X × Y) ∈ closure A ×ˢ closure B := by
      simpa [hEq] using hp
    rcases hp' with ⟨hpA, hpB⟩
    exact ⟨⟨p.1, hpA⟩, ⟨p.2, hpB⟩⟩
  · -- `←` direction
    rintro ⟨hA, hB⟩
    rcases hA with ⟨x, hx⟩
    rcases hB with ⟨y, hy⟩
    -- Build a point in the product of closures.
    have hMem : ((x, y) : X × Y) ∈ closure A ×ˢ closure B := by
      exact And.intro hx hy
    -- Translate the membership back via `hEq`.
    have hProdMem : ((x, y) : X × Y) ∈ closure (A ×ˢ B) := by
      simpa [hEq] using hMem
    exact ⟨(x, y), hProdMem⟩