import LeanServer.HTTP.Types

namespace LeanServer.Web
open LeanServer.HTTP

/-- Template variable bindings -/
abbrev TemplateVars := List (String × String)

/-- Simple template engine with `{{variable}}` interpolation.
    Supports:
    - `{{varName}}`           — variable substitution
    - `{{#if varName}}...{{/if}}` — conditional blocks
    - `{{#each items}}...{{/each}}` — iteration (items = semicolon-separated values)
    - `{{> partialName}}`     — partial inclusion (from a partial map)

    Uses fuel parameter for guaranteed termination. Fuel = template.length
    is sufficient since each recursive call operates on a strictly shorter string. -/
def renderTemplate (template : String) (vars : TemplateVars)
    (tplPartials : List (String × String) := []) : String :=
  renderTemplateAux template vars tplPartials (template.length + 1)
where
  renderTemplateAux (template : String) (vars : TemplateVars)
      (tplPartials : List (String × String)) (fuel : Nat) : String :=
    match fuel with
    | 0 => template  -- Fuel exhausted: return remaining template as-is
    | fuel' + 1 => Id.run do
  let mut result := ""
  let mut i := 0
  let chars := template.toList.toArray
  let len := chars.size
  while i < len do
    if i + 1 < len && chars[i]! == '{' && chars[i + 1]! == '{' then
      -- Find closing }}
      let mut j := i + 2
      while j + 1 < len && ¬(chars[j]! == '}' && chars[j + 1]! == '}') do
        j := j + 1
      if j + 1 < len then
        let tag := (chars.extract (i + 2) j).toList
        let tagStr : String := ((String.ofList tag).trimAscii).toString
        if tagStr.startsWith "#if " then
          -- Conditional: {{#if varName}}...{{/if}}
          let varName : String := ((tagStr.drop 4).toString.trimAscii).toString
          let endTag := "{{/if}}"
          let remaining := String.ofList (chars.extract (j + 2) len).toList
          match remaining.splitOn endTag with
          | body :: rest =>
            let hasValue := vars.find? (fun (k, _) => k == varName) |>.isSome
            if hasValue then
              result := result ++ renderTemplateAux body vars tplPartials fuel'
            result := result ++ renderTemplateAux (String.intercalate endTag rest) vars tplPartials fuel'
            return result
          | [] =>
            result := result ++ "{{TEMPLATE_ERROR: unclosed #if}}"
            i := j + 2
        else if tagStr.startsWith "#each " then
          -- Iteration: {{#each items}}...{{/each}}
          let varName : String := ((tagStr.drop 6).toString.trimAscii).toString
          let endTag := "{{/each}}"
          let remaining := String.ofList (chars.extract (j + 2) len).toList
          match remaining.splitOn endTag with
          | body :: rest =>
            let values := match vars.find? (fun (k, _) => k == varName) with
              | some (_, v) => v.splitOn ";"
              | none => []
            for val in values do
              let itemVars := ("item", val) :: vars
              result := result ++ renderTemplateAux body itemVars tplPartials fuel'
            result := result ++ renderTemplateAux (String.intercalate endTag rest) vars tplPartials fuel'
            return result
          | [] =>
            result := result ++ "{{TEMPLATE_ERROR: unclosed #each}}"
            i := j + 2
        else if tagStr.startsWith "> " then
          -- Partial: {{> partialName}}
          let partialName : String := ((tagStr.drop 2).toString.trimAscii).toString
          match tplPartials.find? (fun (k, _) => k == partialName) with
          | some (_, partialContent) =>
            result := result ++ renderTemplateAux partialContent vars tplPartials fuel'
          | none =>
            result := result ++ "{{PARTIAL_NOT_FOUND: " ++ partialName ++ "}}"
          i := j + 2
        else
          -- Simple variable substitution
          match vars.find? (fun (k, _) => k == tagStr) with
          | some (_, v) => result := result ++ v
          | none        => result := result ++ "{{UNDEFINED: " ++ tagStr ++ "}}"
          i := j + 2
      else
        result := result.push chars[i]!
        i := i + 1
    else
      result := result.push chars[i]!
      i := i + 1
  return result

/-- Render a template and return an HTML response -/
def renderHtml (template : String) (vars : TemplateVars)
    (partials : List (String × String) := []) : Response :=
  Response.html (renderTemplate template vars partials)

/-- Common HTML page wrapper template -/
def layoutTemplate : String :=
  "<!DOCTYPE html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>{{title}}</title>" ++
  "<style>body{font-family:system-ui,sans-serif;max-width:800px;margin:2em auto;padding:0 1em}" ++
  "h1{color:#2d3748}a{color:#3182ce}.card{border:1px solid #e2e8f0;border-radius:8px;padding:1em;margin:1em 0}" ++
  "</style>{{> head}}</head><body>{{> nav}}<main>{{content}}</main>" ++
  "<footer><p>&copy; LeanServer</p></footer></body></html>"

/-- Render content inside the layout -/
def renderPage (title : String) (content : String) (vars : TemplateVars := [])
    (partials : List (String × String) := []) : Response :=
  let allVars := [("title", title), ("content", content)] ++ vars
  let defaultPartials := [("head", ""), ("nav", "")] ++ partials
  renderHtml layoutTemplate allVars defaultPartials

end LeanServer.Web
