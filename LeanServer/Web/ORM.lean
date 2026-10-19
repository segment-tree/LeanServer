import Std

/-! Pure SQL construction retained from Web.Framework. No driver imports.
These legacy string builders accept SQL fragments; applications must use driver
parameters for untrusted values. They do not execute database operations. -/
namespace LeanServer.Web

/-- A database column definition -/
structure Column where
  name     : String
  colType  : String   -- SQL type: "TEXT", "INTEGER", "BOOLEAN", etc.
  nullable : Bool := true
  primaryKey : Bool := false
  deriving Inhabited

/-- Typeclass for types that can be stored in the database -/
class Model (α : Type) where
  tableName : String
  columns   : Array Column
  toRow     : α → Array String
  fromRow   : Array String → Option α

/-- SQL query builder -/
structure QueryBuilder where
  table      : String
  selectCols : List String := ["*"]
  conditions : List String := []
  orderBy    : Option String := none
  limitVal   : Option Nat := none
  offsetVal  : Option Nat := none
  deriving Inhabited

def QueryBuilder.from (table : String) : QueryBuilder :=
  { table := table }

def QueryBuilder.select (qb : QueryBuilder) (cols : List String) : QueryBuilder :=
  { qb with selectCols := cols }

def QueryBuilder.where_ (qb : QueryBuilder) (cond : String) : QueryBuilder :=
  { qb with conditions := qb.conditions ++ [cond] }

def QueryBuilder.orderByAsc (qb : QueryBuilder) (col : String) : QueryBuilder :=
  { qb with orderBy := some s!"{col} ASC" }

def QueryBuilder.orderByDesc (qb : QueryBuilder) (col : String) : QueryBuilder :=
  { qb with orderBy := some s!"{col} DESC" }

def QueryBuilder.limit (qb : QueryBuilder) (n : Nat) : QueryBuilder :=
  { qb with limitVal := some n }

def QueryBuilder.offset (qb : QueryBuilder) (n : Nat) : QueryBuilder :=
  { qb with offsetVal := some n }

/-- Build the final SQL SELECT string -/
def QueryBuilder.toSQL (qb : QueryBuilder) : String := Id.run do
  let cols := String.intercalate ", " qb.selectCols
  let mut sql := s!"SELECT {cols} FROM {qb.table}"
  if qb.conditions.length > 0 then
    let conds := String.intercalate " AND " qb.conditions
    sql := sql ++ s!" WHERE {conds}"
  match qb.orderBy with
  | some ob => sql := sql ++ s!" ORDER BY {ob}"
  | none    => pure ()
  match qb.limitVal with
  | some n  => sql := sql ++ s!" LIMIT {n}"
  | none    => pure ()
  match qb.offsetVal with
  | some n  => sql := sql ++ s!" OFFSET {n}"
  | none    => pure ()
  return sql

/-- Generate INSERT SQL for a model instance -/
def insertSQL [Model α] (obj : α) : String :=
  let cols := (Model.columns (α := α)).map (·.name)
  let vals := (Model.toRow obj).map (fun v => s!"'{v}'")
  let colStr := String.intercalate ", " cols.toList
  let valStr := String.intercalate ", " vals.toList
  s!"INSERT INTO {Model.tableName (α := α)} ({colStr}) VALUES ({valStr})"

/-- Generate UPDATE SQL for a model instance by primary key -/
def updateSQL [Model α] (obj : α) : String := Id.run do
  let cols := Model.columns (α := α)
  let vals := Model.toRow obj
  let mut setClauses : List String := []
  let mut whereClause := ""
  for i in List.range cols.size do
    if i < cols.size && i < vals.size then
      let col := cols[i]!
      let val := vals[i]!
      if col.primaryKey then
        whereClause := s!"{col.name} = '{val}'"
      else
        setClauses := setClauses ++ [s!"{col.name} = '{val}'"]
  let setStr := String.intercalate ", " setClauses
  return s!"UPDATE {Model.tableName (α := α)} SET {setStr} WHERE {whereClause}"

/-- Generate DELETE SQL by primary key value -/
def deleteSQL [Model α] (_dummy : α) (pkValue : String) : String :=
  let cols := Model.columns (α := α)
  match cols.toList.find? (·.primaryKey) with
  | some pk => s!"DELETE FROM {Model.tableName (α := α)} WHERE {pk.name} = '{pkValue}'"
  | none    => s!"DELETE FROM {Model.tableName (α := α)} WHERE id = '{pkValue}'"

/-- Generate CREATE TABLE SQL from a Model definition -/
def createTableSQL (α : Type) [Model α] : String :=
  let cols := Model.columns (α := α)
  let colDefs := cols.map fun c =>
    let nullStr := if c.nullable then "" else " NOT NULL"
    let pkStr := if c.primaryKey then " PRIMARY KEY" else ""
    s!"{c.name} {c.colType}{nullStr}{pkStr}"
  let colStr := String.intercalate ", " colDefs.toList
  s!"CREATE TABLE IF NOT EXISTS {Model.tableName (α := α)} ({colStr})"

end LeanServer.Web
