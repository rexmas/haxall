// Copyright (c) 2026, SkyFoundry LLC
// Licensed under the Academic Free License version 3.0
using xeto
using haystack

** Resolve queries against one library and its concrete dependency closure.
** Recreate the compiler when the schema or its versions change.
class RdfQueryCompiler
{
  new make(Namespace ns, Lib lib)
  {
    this.ns = ns
    this.lib = lib
    addLibrary(lib)
  }

  private Void addLibrary(Lib library)
  {
    previous := libraries[library.name]
    if (previous != null)
    {
      if (previous.version != library.version) throw ArgErr("Conflicting library versions: ${library.name}")
      return
    }
    libraries[library.name] = library
    library.depends.each |dep| { addLibrary(ns.lib(dep.name)) }
  }

  ** Resolve meaning without producing SPARQL or SHACL.
  RdfQueryPlan resolve(Str querySlot)
  {
    return resolveDefinition(querySlot, false)
  }

  private Spec querySpec(Str querySlot)
  {
    local := querySlot
    queryLib := lib
    querySep := local.index("::")
    if (querySep != null)
    {
      queryLib = libraries[local[0..<querySep]] ?: throw ArgErr("Unknown Query library: $querySlot")
      local = local[querySep+2..-1]
    }
    dot := local.indexr(".") ?: throw ArgErr("Expected Owner.query: $querySlot")
    owner := queryLib.spec(local[0..<dot])
    query := RdfExporter.instanceSlot(owner, local[dot+1..-1], libraries.vals)
      ?: throw ArgErr("Unknown Query: $querySlot")
    return query
  }

  private RdfQueryPlan resolveDefinition(Str querySlot, Bool allowBody)
  {
    query := querySpec(querySlot)
    if (query.type.qname != "sys::Query" || (!allowBody && !query.slots.list.isEmpty))
      throw UnsupportedErr("Expected a Query without a named body: $querySlot")
    via := query.meta["via"] as Str
    inverse := query.meta["inverse"] as Str
    direction := RdfQueryDirection.forward
    if (inverse != null)
    {
      if (via != null) throw UnsupportedErr("via and inverse are mutually exclusive: $querySlot")
      if (!inverse.contains("::")) throw UnsupportedErr("inverse must name a fully qualified Query: $inverse")
      inverseName := inverse
      sep := inverseName.index("::")
      inverseLib := libraries[inverseName[0..<sep]] ?: throw ArgErr("Unknown inverse Query library: $inverse")
      localInverse := inverseName[sep+2..-1]
      dotInverse := localInverse.indexr(".") ?: throw ArgErr("Invalid inverse Query name: $inverse")
      inverseOwner := inverseLib.spec(localInverse[0..<dotInverse], false) ?: throw ArgErr("Unknown inverse Query owner: $inverse")
      referenced := inverseOwner.slot(localInverse[dotInverse+1..-1], false) ?: throw ArgErr("Unknown inverse Query: $inverse")
      if (!referenced.isQuery) throw UnsupportedErr("inverse must reference a Query: $inverse")
      via = referenced.meta["via"] as Str ?: throw UnsupportedErr("Referenced inverse Query must have via: $inverse")
      direction = RdfQueryDirection.inverse
    }
    if (via == null) throw UnsupportedErr("Missing via or inverse: $querySlot")
    repetition := via.endsWith("+") ? RdfQueryRepetition.oneOrMore : RdfQueryRepetition.oneHop
    tag := repetition == RdfQueryRepetition.oneOrMore ? via[0..<-1] : via
    step := tag == "id" ? RdfQueryStep.identity : (tag == "spec" ? RdfQueryStep.specReference : RdfQueryStep.reference)
    if (tag.isEmpty || !tag.all |ch| { ch.isAlphaNum && ch < 128 || ch == '_' })
      throw UnsupportedErr("via must name one tag, optionally followed by +: $querySlot")
    target := query.of(false) ?: throw UnsupportedErr("Missing of: $querySlot")
    if (!RdfQueryResultShaclShapes.isRecordType(target))
      throw UnsupportedErr("of must be a record type or a compound of record types: $querySlot")

    properties := Str:Bool[:]
    if (step == RdfQueryStep.specReference) properties[iri("sys::spec")] = true
    classes := Str:Bool[:]
    // A record may declare a Query member as its type even when the requested
    // Query has no body. Body acceptance and result-type membership are separate.
    recordDefinitions(libraries.vals).each |spec|
    {
      if (RdfQueryResultShaclShapes.isRecordType(spec) && step == RdfQueryStep.reference)
      {
        ids := RdfExporter.instancePropertiesForTag(spec, tag, libraries.vals)
        ids.each |id| { properties[iri(id)] = true }
      }
      if (spec.isa(target)) classes[iri(spec.qname)] = true
    }
    traversal := RdfReferenceTraversal(tag, properties.keys.sort, repetition, direction, step)
    sugar := target.isSugar ? resolveSugar(target) : null
    return RdfQueryPlan(query.qname, target, traversal, classes.keys.sort,
      iri("sys::Entity"), iri("sys::hasMarker"), iri("sys::hasRefField"), sugar)
  }

  private RdfSugarMatch resolveSugar(Spec target)
  {
    sugar := target.sugar
    anchors := Str[,]
    recordDefinitions(libraries.vals).each |s| { if (s.isa(sugar.anchor)) anchors.add(iri(s.qname)) }
    constraints := RdfSugarConstraint[,]
    sugar.constraints.each |slot, name|
    {
      properties := Str:Bool[:]
      recordDefinitions(libraries.vals).each |s|
      {
        if (!RdfQueryResultShaclShapes.isRecordType(s)) return
        ids := RdfExporter.instancePropertiesForTag(s, name, libraries.vals)
        ids.each |id| { properties[iri(id)] = true }
      }
      value := slot.meta["val"]
      kind := RdfSugarValueKind.presence
      if (!slot.isMarker)
      {
        switch (slot.type.qname)
        {
          case "sys::Str": kind = RdfSugarValueKind.string
          case "sys::Bool": kind = RdfSugarValueKind.boolean
          case "sys::Int": kind = RdfSugarValueKind.integer
          case "sys::Number": kind = RdfSugarValueKind.number
          default: throw UnsupportedErr("${slot.qname}: sugar invariant requires Str, Bool, Int, or finite unitless Number")
        }
      }
      if (kind == RdfSugarValueKind.number)
      {
        number := value as Number
        if (number == null || number.unit != null || number.isSpecial)
          throw UnsupportedErr("${slot.qname}: sugar invariant requires a finite unitless Number")
      }
      constraints.add(RdfSugarConstraint(properties.keys.sort, kind, value))
    }
    return RdfSugarMatch(anchors.sort, constraints)
  }

  ** Bind a source and produce all artifacts needed by standard RDF tools.
  RdfQueryArtifacts compile(Str querySlot, Str subjectIri)
  {
    plan := resolve(querySlot)
    sparql := RdfQuerySparqlCompiler(plan)
    return RdfQueryArtifacts(plan, sparql.compile, sparql.compile(subjectIri),
      RdfQueryInputShaclCompiler(plan).compile(subjectIri),
      RdfQueryResultShaclShapes.compile(ns, plan.resultType))
  }

  ** Compile independent requirement matches and SHACL cardinality. The temporary
  ** graph is validation evidence, not stored data or queryNamed assignments.
  RdfQueryBodyValidationArtifacts compileBodyValidation(Str querySlot, Str subjectIri)
  {
    query := querySpec(querySlot)
    original := resolveDefinition(querySlot, true)
    plan := planForTarget(original, original.resultType)
    extent := RdfQuerySparqlCompiler(plan).compile(subjectIri)
    claimExtent := RdfQuerySparqlCompiler(plan).compile(subjectIri, "?claim")
    definitions := recordDefinitions(libraries.vals)
    keys := Str:Str[:]
    anchors := Str:Str[][:]
    query.slots.each |member, key| { keys[member.qname] = key; anchors[key] = Str[,] }
    definitions.each |candidate|
    {
      for (Spec? s := candidate; s != null; s = s.base)
      {
        key := keys[s.qname]
        if (key == null) continue
        anchors[key].add(iri(candidate.qname))
        break
      }
    }
    all := Str[,]
    anchors.each |values| { all.addAll(values) }
    anyAnchor := anchorFilter(all)
    subject := RdfQuerySparqlCompiler.iriToken(subjectIri)
    branches := Str[,]
    shapes := StrBuf().add("@prefix sh: <http://www.w3.org/ns/shacl#> .\n")
    names := Str:Str[:]
    query.slots.each |member, key|
    {
      matching := RdfQuerySparqlCompiler(planForTarget(plan, member)).renderResultMatch
      anchor := anchorFilter(anchors[key])
      claimAnchor := anchorFilter(anchors[key], "?claim")
      claim := "SELECT ?claim WHERE { { $claimExtent } FILTER($claimAnchor) }"
      predicateIri := iri("${query.qname}.$key")
      predicate := RdfQuerySparqlCompiler.iriToken(predicateIri)
      branches.add("{ { $extent } FILTER($anchor) BIND($predicate AS ?requirement) }")
      branches.add("{ { $extent } FILTER(!($anyAnchor)) $matching FILTER NOT EXISTS { { $claim } } BIND($predicate AS ?requirement) }")
      min := member.isMaybe ? 0 : 1
      shapes.add("[] a sh:NodeShape ; sh:targetNode $subject ; sh:property [ sh:path $predicate ; sh:minCount $min ; sh:maxCount 1 ] .\n")
      names[predicateIri] = key
    }
    matches := branches.isEmpty ? "FILTER(false)" : branches.join(" UNION\n")
    return RdfQueryBodyValidationArtifacts(plan.querySlot,
      "CONSTRUCT { $subject ?requirement ?result } WHERE { $matches }",
      RdfQueryInputShaclCompiler(plan).compile(subjectIri), shapes.toStr, names)
  }

  private RdfQueryPlan planForTarget(RdfQueryPlan original, Spec target)
  {
    if (!RdfQueryResultShaclShapes.isRecordType(target))
      throw UnsupportedErr("Query requirement must be a record type: $target.qname")
    classes := recordDefinitions(libraries.vals).findAll |s| { s.isa(target) }.map |s->Str| { iri(s.qname) }
    return RdfQueryPlan(original.querySlot, target, original.traversal, classes,
      original.entityClassIri, original.markerPredicateIri, original.hasRefFieldPredicateIri,
      target.isSugar ? resolveSugar(target) : null)
  }

  ** Membership established by exported nominal subclass paths.
  ** Union edges point from alternatives to the union, never the reverse.
  internal static Bool hasNominalClassPath(Spec candidate, Spec target)
  {
    if (candidate.qname == target.qname) return true
    if (candidate.isAnd && candidate.ofs(false) != null &&
        candidate.ofs.any |base| { hasNominalClassPath(base, target) }) return true
    if (target.isOr && target.ofs(false) != null &&
        target.ofs.any |base| { hasNominalClassPath(candidate, base) }) return true
    if (candidate.isCompound) return false
    return candidate.base != null && hasNominalClassPath(candidate.base, target)
  }

  ** Record type identities shared by selection and returned-record constraints.
  internal static Spec[] recordDefinitions(Lib[] libraries)
  {
    definitions := Str:Spec[:]
    libraries.each |library|
    {
      library.types.each |type| { definitions[type.qname] = type }
      // Contributions are not record types, but their Query members are valid
      // declared record types and must participate in selection and claims.
      library.types.list.dup.addAll(library.mixins.list).each |Spec type|
      {
        type.slots.each |slot|
        {
          if (!slot.isQuery) return
          slot.slots.each |member| { definitions[member.qname] = member }
        }
      }
    }
    return definitions.vals
  }

  private Str anchorFilter(Str[] classes, Str resultVar := "?result")
  {
    if (classes.isEmpty) return "false"
    values := classes.map |s->Str| { RdfQuerySparqlCompiler.iriToken(s) }.join(" ")
    predicate := RdfQuerySparqlCompiler.iriToken(iri("sys::spec"))
    return "EXISTS { $resultVar $predicate ?declaredSpec . VALUES ?declaredSpec { $values } }"
  }

  private Str iri(Str qname)
  {
    sep := qname.index("::") ?: throw ArgErr("Expected qualified name: $qname")
    library := libraries[qname[0..<sep]] ?: throw ArgErr("Missing library for $qname")
    local := Uri.encodeToken(qname[sep+2..-1], Uri.sectionFrag)
    return "http://xeto.dev/rdf/${library.name}-${library.version}#$local"
  }

  private Namespace ns
  private Lib lib
  private Str:Lib libraries := [:]
}

** Portable validation of a Query body's requirement counts.
const class RdfQueryBodyValidationArtifacts
{
  internal new make(Str querySlot, Str constructSparql, Str inputShapes,
                    Str bodyShapes, Str:Str requirementNameByIri)
  {
    this.querySlot = querySlot
    this.constructSparql = constructSparql
    this.inputShapes = inputShapes
    this.bodyShapes = bodyShapes
    this.requirementNameByIri = requirementNameByIri.toImmutable
  }
  const Str querySlot
  const Str constructSparql
  const Str inputShapes
  const Str bodyShapes
  const Str:Str requirementNameByIri
}

//////////////////////////////////////////////////////////////////////////
// RdfQueryPlan
//////////////////////////////////////////////////////////////////////////

** Resolved query meaning. Only the compiler constructs a plan; callers cannot
** change its selected type independently of its result classes.
const class RdfQueryPlan
{
  internal new make(Str querySlot, Spec resultType, RdfReferenceTraversal traversal,
                    Str[] resultClassIris, Str entityClassIri,
                    Str markerPredicateIri, Str hasRefFieldPredicateIri, RdfSugarMatch? sugar := null)
  {
    this.querySlot = querySlot
    this.resultType = resultType
    this.traversal = traversal
    this.resultClassIris = resultClassIris.toImmutable
    this.entityClassIri = entityClassIri
    this.markerPredicateIri = markerPredicateIri
    this.hasRefFieldPredicateIri = hasRefFieldPredicateIri
    this.sugar = sugar
  }

  const Str querySlot
  const Spec resultType
  const RdfReferenceTraversal traversal
  const Str[] resultClassIris
  const Str entityClassIri
  const Str markerPredicateIri
  const Str hasRefFieldPredicateIri
  const RdfSugarMatch? sugar
}

** Structural fallback, independent of traversal and returned-record validation.
const class RdfSugarMatch
{
  internal new make(Str[] anchors, RdfSugarConstraint[] constraints)
  {
    this.anchorClassIris = anchors.toImmutable
    this.constraints = constraints.toImmutable
  }
  const Str[] anchorClassIris
  const RdfSugarConstraint[] constraints
}

const class RdfSugarConstraint
{
  internal new make(Str[] properties, RdfSugarValueKind kind, Obj? value)
  {
    this.propertyIris = properties.toImmutable
    this.kind = kind
    this.value = value
  }
  const Str[] propertyIris
  const RdfSugarValueKind kind
  const Obj? value
}

enum class RdfSugarValueKind { presence, string, boolean, integer, number }

** The tag's RDF properties and the number of steps are independent choices.
const class RdfReferenceTraversal
{
  internal new make(Str tag, Str[] propertyIris, RdfQueryRepetition repetition, RdfQueryDirection direction, RdfQueryStep step)
  {
    this.tag = tag
    this.propertyIris = propertyIris.toImmutable
    this.repetition = repetition
    this.direction = direction
    this.step = step
  }
  const Str tag
  const Str[] propertyIris
  const RdfQueryRepetition repetition
  const RdfQueryDirection direction
  const RdfQueryStep step
}

enum class RdfQueryRepetition { oneHop, oneOrMore }
enum class RdfQueryDirection { forward, inverse }
enum class RdfQueryStep { reference, identity, specReference }

** Portable output: check inputs, execute SELECT, then optionally validate
** returned identities using resultShapes against the complete input graph.
const class RdfQueryArtifacts
{
  internal new make(RdfQueryPlan plan, Str sparql, Str boundSparql,
                    Str inputShapes, RdfQueryResultShaclShapes resultShapes)
  {
    this.plan = plan
    this.sparql = sparql
    this.boundSparql = boundSparql
    this.inputShapes = inputShapes
    this.resultShapes = resultShapes
  }
  const RdfQueryPlan plan
  const Str sparql
  const Str boundSparql
  const Str inputShapes
  const RdfQueryResultShaclShapes resultShapes
}

//////////////////////////////////////////////////////////////////////////
// RdfQuerySparqlCompiler
//////////////////////////////////////////////////////////////////////////

** Serialize the supported semantic constructs as a unique, unordered SELECT.
internal class RdfQuerySparqlCompiler
{
  new make(RdfQueryPlan plan) { this.plan = plan }

  Str compile(Str? subjectIri := null, Str resultVar := "?result")
  {
    out := StrBuf().add("SELECT DISTINCT $resultVar WHERE {\n")
    if (subjectIri != null) out.add("  VALUES ?subject { ${iriToken(subjectIri)} }\n")
    switch (plan.traversal.step)
    {
      case RdfQueryStep.identity: out.add("  BIND(?subject AS $resultVar)\n")
      case RdfQueryStep.reference:
      case RdfQueryStep.specReference:
        path := "(" + plan.traversal.propertyIris.map |p->Str| { iriToken(p) }.join("|") + ")"
        path = directionPrefix + path
        path += repetitionSuffix(plan.traversal.repetition)
        out.add("  ?subject $path $resultVar .\n")
      default: throw UnsupportedErr("Unsupported query step")
    }
    out.add("  $resultVar a ${iriToken(plan.entityClassIri)} .\n")
    out.add("  FILTER(isIRI($resultVar))\n")
    if (plan.traversal.step != RdfQueryStep.identity && plan.traversal.direction == RdfQueryDirection.inverse && plan.traversal.repetition == RdfQueryRepetition.oneHop)
    {
      // Native direct inverse compares IDs without dereferencing non-Refs.
      properties := plan.traversal.propertyIris.map |p->Str| { iriToken(p) }.join(" ")
      out.add("  FILTER EXISTS { VALUES ?referenceProperty { $properties } $resultVar ${iriToken(plan.hasRefFieldPredicateIri)} ?referenceProperty ; ?referenceProperty ?subject . }\n")
    }
    out.add(renderResultMatch(resultVar))
    return out.add("}\n").toStr
  }

  internal Str renderResultMatch(Str resultVar := "?result")
  {
    out := StrBuf()
    classes := plan.resultClassIris.map |p->Str| { iriToken(p) }.join(" ")
    nominal := "EXISTS { $resultVar a ?resultType . VALUES ?resultType { $classes } }"
    sugar := plan.sugar
    if (sugar == null) out.add("  FILTER($nominal)\n")
    else
    {
      anchors := sugar.anchorClassIris.map |p->Str| { iriToken(p) }.join(" ")
      predicates := ["EXISTS { $resultVar a ?resultType . VALUES ?resultType { $anchors } }"]
      sugar.constraints.each |constraint, index|
      {
        properties := constraint.propertyIris.map |p->Str| { iriToken(p) }.join(" ")
        property := "?sugarProperty$index"
        value := "?sugarValue$index"
        stored := "EXISTS { VALUES $property { $properties } $resultVar $property $value ."
        switch (constraint.kind)
        {
          case RdfSugarValueKind.presence: predicates.add("($stored } || EXISTS { VALUES $property { $properties } $resultVar ${iriToken(plan.markerPredicateIri)} $property . } || EXISTS { VALUES $property { $properties } $resultVar ${iriToken(plan.hasRefFieldPredicateIri)} $property . })")
          case RdfSugarValueKind.string: predicates.add("$stored FILTER($value = ${RdfExporter.stringLiteral(constraint.value)}) }")
          case RdfSugarValueKind.boolean: predicates.add("$stored FILTER($value = $constraint.value) }")
          case RdfSugarValueKind.integer: predicates.add("$stored FILTER(datatype($value) IN (<http://www.w3.org/2001/XMLSchema#integer>, <http://www.w3.org/2001/XMLSchema#double>) && $value = $constraint.value) }")
          case RdfSugarValueKind.number: predicates.add("$stored FILTER(datatype($value) = <http://www.w3.org/2001/XMLSchema#double> && $value = $constraint.value) }")
          default: throw UnsupportedErr("Unsupported sugar constraint: $constraint.kind")
        }
      }
      structural := predicates.join(" && ")
      out.add("  FILTER($nominal || ($structural))\n")
    }
    return out.toStr
  }

  private Str directionPrefix()
  {
    switch (plan.traversal.direction)
    {
      case RdfQueryDirection.forward: return ""
      case RdfQueryDirection.inverse: return "^"
      default: throw UnsupportedErr("Unsupported query direction")
    }
  }

  private Str repetitionSuffix(RdfQueryRepetition repetition)
  {
    switch (repetition)
    {
      case RdfQueryRepetition.oneHop: return ""
      case RdfQueryRepetition.oneOrMore: return "+"
      default: throw UnsupportedErr("Unsupported query repetition: $repetition")
    }
  }

  ** Both syntaxes use absolute IRI tokens, never interpolated raw user text.
  internal static Str iriToken(Str iri)
  {
    if (!iri.contains(":") || iri.any |ch| { ch <= 32 || "<>\"{}|^`\\".containsChar(ch) })
      throw ArgErr("Invalid RDF IRI: $iri")
    return "<$iri>"
  }

  private RdfQueryPlan plan
}

//////////////////////////////////////////////////////////////////////////
// RdfQueryInputShaclCompiler
//////////////////////////////////////////////////////////////////////////

** Check source existence and native dereference errors. These are execution
** preconditions, separate from conformance of returned records.
internal class RdfQueryInputShaclCompiler
{
  new make(RdfQueryPlan plan) { this.plan = plan }

  Str compile(Str subjectIri)
  {
    source := RdfQuerySparqlCompiler.iriToken(subjectIri)
    entity := RdfQuerySparqlCompiler.iriToken(plan.entityClassIri)
    startingRecord := "@prefix sh: <http://www.w3.org/ns/shacl#> .\n" +
      "@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .\n" +
      "[] a sh:NodeShape ; sh:targetNode $source ; sh:nodeKind sh:IRI ;\n" +
      "sh:property [ sh:path rdf:type ; sh:hasValue $entity ]\n"
    switch (plan.traversal.step)
    {
      case RdfQueryStep.identity: return startingRecord + ".\n"
      case RdfQueryStep.reference:
      case RdfQueryStep.specReference: return startingRecord + referenceChecks(entity)
      default: throw UnsupportedErr("Unsupported query step")
    }
  }

  private Str referenceChecks(Str entity)
  {
    properties := plan.traversal.propertyIris.map |p->Str| { RdfQuerySparqlCompiler.iriToken(p) }
    paths := properties.join(" ")
    path := properties.size == 1 ? properties.first : "[ sh:alternativePath ( $paths ) ]"
    checks := StrBuf()
    evidence := RdfQuerySparqlCompiler.iriToken(plan.hasRefFieldPredicateIri)
    // A dangling Ref is still a Ref. Check the owning field's stored value
    // kind, rather than requiring the referenced record to exist.
    properties.each |property|
    {
      checks.add("sh:node [ sh:message \"Missing reference-field evidence\" ; sh:or (\n")
      checks.add(" [ sh:property [ sh:path $property ; sh:maxCount 0 ] ]\n")
      checks.add(" [ sh:property [ sh:path $evidence ; sh:hasValue $property ] ]\n")
      checks.add(") ] ;\n")
    }
    checks.add("sh:property [ sh:path $path ; sh:nodeKind sh:IRI ; sh:message \"Invalid reference value: expected an IRI\" ] ;\n")
    marker := RdfQuerySparqlCompiler.iriToken(plan.markerPredicateIri)
    checks.add("sh:property [ sh:path $marker ; sh:not [ sh:in ( $paths ) ] ; sh:message \"Invalid reference value: Marker\" ]")
    traversal := checks.toStr
    switch (plan.traversal.repetition)
    {
      case RdfQueryRepetition.oneHop: traversal = checks.toStr
      case RdfQueryRepetition.oneOrMore:
        traversal = "sh:property [ sh:path [ sh:zeroOrMorePath $path ] ; sh:node [ $traversal ] ]"
      default: throw UnsupportedErr("Unsupported query repetition: ${plan.traversal.repetition}")
    }
    // Inverse scans all records with the tag, rather than the source's outgoing
    // component. Direct inverse only compares IDs and needs no dereference checks.
    switch (plan.traversal.direction)
    {
      case RdfQueryDirection.forward: traversal = ";\n" + traversal
      case RdfQueryDirection.inverse:
        switch (plan.traversal.repetition)
        {
          case RdfQueryRepetition.oneHop: traversal = ""
          case RdfQueryRepetition.oneOrMore:
            traversal = ".\n[] a sh:NodeShape ; sh:targetClass $entity ; ${checks}"
          default: throw UnsupportedErr("Unsupported query repetition")
        }
      default: throw UnsupportedErr("Unsupported query direction")
    }
    return "$traversal .\n"
  }

  private RdfQueryPlan plan
}

//////////////////////////////////////////////////////////////////////////
// RdfQueryResultShaclShapes
//////////////////////////////////////////////////////////////////////////

** Reusable constraints for records returned by a Query's 'of' type.
** Consumers add sh:targetNode after execution; these shapes have no targets.
const class RdfQueryResultShaclShapes
{
  internal static Bool isRecordType(Spec type)
  {
    if (type.isDict) return true
    members := type.ofs(false)
    return members != null && !members.isEmpty && members.all |member| { isRecordType(member) }
  }

  static RdfQueryResultShaclShapes compile(Namespace ns, Spec resultType)
  {
    if (!isRecordType(resultType)) throw UnsupportedErr("Query-result conformance requires a record type: ${resultType.qname}")
    buffer := Buf()
    exporter := RdfExporter((MNamespace)ns, buffer.out, Etc.dict0)
    exporter.queryResultShapes(resultType).flush
    iri := "http://xeto.dev/rdf/${resultType.lib.name}-${resultType.lib.version}#${resultType.name}/constraints"
    return make(buffer.flip.readAllStr, iri)
  }

  private new make(Str turtleShapes, Str resultShapeIri)
  {
    this.turtleShapes = turtleShapes
    this.resultShapeIri = resultShapeIri
  }

  const Str turtleShapes
  const Str resultShapeIri
}
