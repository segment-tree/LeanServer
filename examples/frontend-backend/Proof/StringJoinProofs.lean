module
import all Init.Data.String.Defs
import Init.Data.String.Lemmas

/-! Equations for the actual accumulator-based String.intercalate. -/

public section
namespace FrontendBackend.HTTPStrings
private theorem intercalate_go_prefix (sep pre acc : String) (xs : List String) :
    String.intercalate.go (pre ++ acc) sep xs = pre ++ String.intercalate.go acc sep xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [String.intercalate.go, String.append_assoc, ih]

theorem intercalate_one (sep s : String) : sep.intercalate [s] = s := by simp [String.intercalate, String.intercalate.go]

theorem intercalate_cons (sep a b : String) (xs : List String) :
    sep.intercalate (a :: b :: xs) = a ++ sep ++ sep.intercalate (b :: xs) := by
  exact intercalate_go_prefix sep (a ++ sep) b xs
end FrontendBackend.HTTPStrings
