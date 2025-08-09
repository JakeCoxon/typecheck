import { ProgramBuilder, type Loc, dummy, Program, type Node } from "./typecheck";

// Helper functions to create nodes
const nodeFac = {
  intLiteral: (value: number, loc: Loc = dummy): Node => ({ location: loc, kind: "IntLiteral", value }),
  boolLiteral: (value: boolean, loc: Loc = dummy): Node => ({ location: loc, kind: "BoolLiteral",  value }),
  var: (name: string, loc: Loc = dummy): Node => ({ location: loc, kind: "Var", name }),
  app: (fnIndex: number, argsIndices: number[], typeArgsIndices: number[] = [], loc: Loc = dummy): Node => ({ location: loc, kind: "App", fnIndex, argsIndices, typeArgsIndices }),
  funDecl: (name: string, paramsIndices: number[], typeParamsIndices: number[], returnTypeIndex: number, bodyIndex: number, traitBounds?: [string, number][], subtypeBounds?: [string, number][], loc: Loc = dummy): Node => ({ location: loc, kind: "FunDecl", name, paramsIndices, typeParamsIndices, returnTypeIndex, bodyIndex, traitBounds, subtypeBounds }),
  let: (name: string, valueIndex: number, typeIndex?: number, loc: Loc = dummy): Node => ({ location: loc, kind: "Let", name, valueIndex, typeIndex }),
  if: (condIndex: number, thenIndex: number, elseIndex?: number, loc: Loc = dummy): Node => ({ location: loc, kind: "If", condIndex, thenIndex, elseIndex }),
  statements: (statementsIndices: number[], loc: Loc = dummy): Node => ({ location: loc, kind: "Statements", statementsIndices }),
  funParam: (name: string, typeIndex: number, loc: Loc = dummy): Node => ({ location: loc, kind: "FunParam", name, typeIndex }),
  typeApp: (baseIndex: number, typeArgsIndices: number[], loc: Loc = dummy): Node => ({ location: loc, kind: "TypeApp", baseIndex, typeArgsIndices }),
}


// ===== Test Builder Class =====
// Dedicated class for building nodes in tests with short method names
export class TestBuilder {
  constructor(public builder: ProgramBuilder) {}

  // Primitive literals
  int(value: number, loc: Loc = dummy): number {
    return this.builder.addNode(nodeFac.intLiteral(value, loc));
  }

  bool(value: boolean, loc: Loc = dummy): number {
    return this.builder.addNode(nodeFac.boolLiteral(value, loc));
  }

  // Variables and references
  var(name: string, loc: Loc = dummy): number {
    return this.builder.addNode(nodeFac.var(name, loc));
  }

  // Function applications
  app(fnIndex: number, argIndex: number, loc: Loc = dummy): number {
    return this.builder.addNode(nodeFac.app(fnIndex, [argIndex], [], loc));
  }

  appN(fnIndex: number, argIndices: number[], loc: Loc = dummy): number {
    return this.builder.addNode(nodeFac.app(fnIndex, argIndices, [], loc));
  }

  // Lambda functions
  lam(paramName: string, bodyIndex: number, loc: Loc = dummy): number {
    const paramIndex = this.builder.addNode(nodeFac.funParam(paramName, -1, loc));
    return this.builder.addNode(nodeFac.funDecl("", [paramIndex], [], 0, bodyIndex, [], [], loc));
  }

  lamN(paramNames: string[], bodyIndex: number, loc: Loc = dummy): number {
    const paramIndices = paramNames.map(name => 
      this.builder.addNode(nodeFac.funParam(name, -1, loc))
    );
    return this.builder.addNode(nodeFac.funDecl("", paramIndices, [], 0, bodyIndex, [], [], loc));
  }

  // Control flow
  if(condIndex: number, thenIndex: number, elseIndex: number, loc: Loc = dummy): number {
    return this.builder.addNode(nodeFac.if(condIndex, thenIndex, elseIndex, loc));
  }

  // Bindings
  let(name: string, annotation: number | null, value: number | null, loc: Loc = dummy): number {
    const valueIndex = value !== null ? value : -1;
    const typeIndex = annotation !== null ? annotation : undefined;
    return this.builder.addNode(nodeFac.let(name, valueIndex, typeIndex, loc));
  }

  // Block of statements
  block(...stmtIndices: number[]): number {
    return this.builder.addNode(nodeFac.statements(stmtIndices, this.getLoc(stmtIndices)));
  }

  // Type applications
  typeApp(ctorName: string, typeArgNames: (string | number)[], loc: Loc = dummy): number {
    const ctorIndex = this.var(ctorName, loc);
    const argIndices = typeArgNames.map(name => typeof name === "number" ? name : this.var(name, loc));
    return this.builder.addNode(nodeFac.typeApp(ctorIndex, argIndices, loc));
  }

  // Generic function declaration
  funDecl(name: string, typeParams: string[], params: string[], bodyIndex: number, paramTypes?: string[], returnType?: string, traitBounds?: [string, string][], subtypeBounds?: [string, string][], loc: Loc = dummy): number {
    // Add type parameters
    const typeParamIndices: number[] = [];
    for (const typeParam of typeParams) {
      const typeParamIndex = this.builder.addNode({
        location: loc,
        kind: "TypeParam",
        name: typeParam,
        constraintsIndices: []
      });
      typeParamIndices.push(typeParamIndex);
    }

    // Add function parameters
    const paramIndices: number[] = [];
    for (let i = 0; i < params.length; i++) {
      const typeIndex = paramTypes?.[i] ? this.var(paramTypes[i]!) : -1;
      const paramIndex = this.builder.addNode(nodeFac.funParam(params[i]!, typeIndex, loc));
      paramIndices.push(paramIndex);
    }
    
    const returnTypeIndex = returnType ? this.var(returnType) : 0;
    const traitBoundIndices = traitBounds?.map(([tvar, trait]) => [tvar, this.var(trait)] as [string, number]);
    const subtypeBoundIndices = subtypeBounds?.map(([tvar, subtype]) => [tvar, this.var(subtype)] as [string, number]);
    
    return this.builder.addNode(nodeFac.funDecl(name, paramIndices, typeParamIndices, returnTypeIndex, bodyIndex, traitBoundIndices, subtypeBoundIndices, loc));
  }

  // Enhanced function declaration with keyword arguments for complex cases
  complexFunDecl(options: {
    name: string,
    typeParams?: string[],
    params: string[],
    bodyIndex: number,
    paramTypes?: string[],
    returnType?: string,
    traitBounds?: Array<{ typeParam: string, trait: string }>,
    subtypeBounds?: Array<{ typeParam: string, subtype: string }>,
    loc?: Loc
  }): number {
    const {
      name,
      typeParams = [],
      params,
      bodyIndex,
      paramTypes,
      returnType,
      traitBounds,
      subtypeBounds,
      loc = dummy
    } = options;

    // Convert traitBounds and subtypeBounds to the format expected by funDecl
    const traitBoundsArray = traitBounds?.map(({ typeParam, trait }) => [typeParam, trait] as [string, string]);
    const subtypeBoundsArray = subtypeBounds?.map(({ typeParam, subtype }) => [typeParam, subtype] as [string, string]);

    return this.funDecl(name, typeParams, params, bodyIndex, paramTypes, returnType, traitBoundsArray, subtypeBoundsArray, loc);
  }

  // Build final program
  program(rootIndex: number): Program {
    this.builder.types = new Array(this.builder.nodes.length).fill(null);
    const program = new Program(this.builder.nodes, this.builder.types, rootIndex, this.builder.schemes, this.builder.apps, this.builder.instantiations);
    this.builder.program = program;
    return program;
  }

  // Helper to get location from nodes
  private getLoc(indices: number[]): Loc {
    if (indices.length > 0) {
      const firstNode = this.builder.nodes[indices[0]!];
      return firstNode?.location || dummy;
    }
    return dummy;
  }
}