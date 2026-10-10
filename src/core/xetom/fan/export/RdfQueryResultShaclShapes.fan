// Copyright (c) 2026, SkyFoundry LLC
// Licensed under the Academic Free License version 3.0
using xeto
using haystack

** Reusable constraints for records returned by a Query's 'of' type.
** Consumers add sh:targetNode after execution; these shapes have no targets.
class RdfQueryResultShaclShapes
{
  static RdfQueryResultShaclShapes compile(Namespace ns, Spec resultType)
  {
    if (!resultType.isDict) throw UnsupportedErr("Query-result conformance requires a Dict type: ${resultType.qname}")
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
