namespace Zklib.Core

namespace Radix2Representation

universe u

/--
The canonical finite table representation used across radix-2 implementations.
-/
abbrev Table (α : Type u) (n : Nat) := Fin n -> α

/--
View a finite table as a list in canonical index order.
-/
def listOfTable {α : Type u} {n : Nat} (values : Table α n) : List α :=
  List.ofFn values

/--
View a finite table as an array in canonical index order.
-/
def arrayOfTable {α : Type u} {n : Nat} (values : Table α n) : Array α :=
  Array.ofFn values

/--
Interpret a length-indexed list as a canonical finite table.
-/
def tableOfList {α : Type u} {n : Nat} (values : List α) (h : values.length = n) : Table α n :=
  fun i => values[i.1]'(by exact h.symm ▸ i.2)

/--
Interpret a size-indexed array as a canonical finite table.
-/
def tableOfArray {α : Type u} {n : Nat} (values : Array α) (h : values.size = n) : Table α n :=
  fun i => values[i.1]'(by exact h.symm ▸ i.2)

@[simp]
theorem length_listOfTable {α : Type u} {n : Nat} (values : Table α n) :
    (listOfTable values).length = n := by
  simp [listOfTable]

@[simp]
theorem size_arrayOfTable {α : Type u} {n : Nat} (values : Table α n) :
    (arrayOfTable values).size = n := by
  simp [arrayOfTable]

@[simp]
theorem tableOfList_listOfTable {α : Type u} {n : Nat} (values : Table α n) :
    tableOfList (listOfTable values) (length_listOfTable values) = values := by
  funext i
  simp [tableOfList, listOfTable]

@[simp]
theorem arrayOfTable_toList {α : Type u} {n : Nat} (values : Table α n) :
    (arrayOfTable values).toList = listOfTable values := by
  simp [arrayOfTable, listOfTable]

@[simp]
theorem tableOfArray_arrayOfTable {α : Type u} {n : Nat} (values : Table α n) :
    tableOfArray (arrayOfTable values) (size_arrayOfTable values) = values := by
  funext i
  simp [tableOfArray, arrayOfTable]

theorem tableOfArray_eq_tableOfList_toList {α : Type u} {n : Nat}
    (values : Array α) (h : values.size = n) :
    tableOfArray values h =
      tableOfList values.toList (by rw [Array.length_toList, h]) := by
  funext i
  simp [tableOfArray, tableOfList]

end Radix2Representation

end Zklib.Core
