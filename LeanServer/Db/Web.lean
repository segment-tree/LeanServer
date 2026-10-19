import LeanServer.Db.PostgreSQL
import LeanServer.Db.MySQL
import Lean.Data.Json

/-! Optional query helpers formerly embedded in WebApplication.
The updated manager is returned explicitly; applications decide how it is stored
in their ReaderT/StateT environment and synchronized across requests. -/
namespace LeanServer

def executePgQuery (manager : DatabaseManager PostgreSQLDriver) (query : String) :=
  executeQueryWithPool manager query

def executeMySqlQuery (manager : DatabaseManager MySQLDriver) (query : String) :=
  executeQueryWithPool manager query

def queryResultToJson (result : QueryResult) : String :=
  (Lean.Json.arr (result.rows.map fun row =>
    Lean.Json.mkObj ((List.range (min result.columns.size row.size)).map fun i =>
      (result.columns[i]!, Lean.toJson row[i]!)))).compress

end LeanServer
