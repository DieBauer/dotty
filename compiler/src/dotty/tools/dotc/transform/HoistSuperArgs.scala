package dotty.tools.dotc
package transform

import MegaPhase._
import core.DenotTransformers._
import core.Symbols._
import core.Contexts._
import ast.TreeTypeMap
import core.Types._
import core.Flags._
import core.Decorators._
import collection.mutable
import ast.Trees._
import core.NameKinds.SuperArgName
import SymUtils._

object HoistSuperArgs {
  val name: String = "hoistSuperArgs"
}

/** This phase hoists complex arguments of supercalls and this-calls out of the enclosing class.
 *  Example:
 *
 *      class B(y: Int) extends A({ def f(x: Int) = x * x; f(y)})
 *
 *  is translated to
 *
 *      class B(y: Int) extends A(B#B$superArg$1(this.y)) {
 *        private <static> def B$superArg$1(y: Int): Int = {
 *          def f(x: Int): Int = x.*(x); f(y)
 *        }
 *      }
 *
 *  An argument is complex if it contains a method or template definition, a this or a new,
 *  or it contains an identifier which needs a `this` prefix to be accessed. This is the case
 *  if the identifier has neither a global reference nor a reference to a parameter of the enclosing class.
 *  @see needsHoist for an implementation.
 *
 *  A hoisted argument definition gets the parameters of the class it is hoisted from
 *  as method parameters. The definition is installed in the scope enclosing the class,
 *  or, if that is a package, it is made a static method of the class itself.
 */
class HoistSuperArgs extends MiniPhase with IdentityDenotTransformer { thisPhase =>
  import ast.tpd._

  def phaseName: String = HoistSuperArgs.name

  override def runsAfter: Set[String] = Set(ByNameClosures.name)
    // By name closures need to be introduced first in order to be hoisted out here.
    // There's an interaction with by name closures in that the <cbn-arg> marker
    // application should not be hoisted, but be left at the point of call.

  /** Defines methods for hoisting complex supercall arguments out of
   *  parent super calls and constructor definitions.
   *  Hoisted superarg methods are collected in `superArgDefs`
   */
  class Hoister(cls: Symbol)(implicit ctx: Context) {
    System.out.println(s"new Hoister for cls: $cls")
    val superArgDefs: mutable.ListBuffer[DefDef] = new mutable.ListBuffer

    /** If argument is complex, hoist it out into its own method and refer to the
     *  method instead.
     *  @param   arg   The argument that might be hoisted
     *  @param   cdef  The definition of the constructor from which the call is made
     *  @return  The argument after possible hoisting
     */
    private def hoistSuperArg(arg: Tree, cdef: DefDef): Tree = {
      System.out.println(s"hoistSuperArg $arg with defdef $cdef")
      val constr = cdef.symbol
      System.out.println(s"hoistSuperArg.constr: $constr")

      lazy val origParams = // The parameters that can be accessed in the supercall
        if (constr == cls.primaryConstructor) {
          System.out.println("is primaryconstructor:")
          val t = cls.info.decls.filter(d => d.is(TypeParam) || d.is(ParamAccessor))
          System.out.println(s"cls.info.decls:")
          cls.info.decls.foreach(System.out.println)
          System.out.println(s"Filter: $t")
          t
        } else
          allParamSyms(cdef)

      /** The parameter references defined by the constructor info */
      def allParamRefs(tp: Type): List[ParamRef] = {
        System.out.println(s"allParamRefs $tp")
        tp match {
          case tp: LambdaType =>
            System.out.println(s"allParamRefs.lambdatype: $tp")
            tp.paramRefs ++ allParamRefs(tp.resultType)
          case _              =>
            System.out.println(s"allParamRefs._: $tp")
            Nil
        }
      }

      /** Splice `restpe` in final result type position of `tp` */
      def replaceResult(tp: Type, restpe: Type): Type = {
        System.out.println(s"replaceResult $tp and res $restpe")

        tp match {
          case tp: LambdaType =>
            System.out.println(s"replaceResult.lambdatype: $tp")
            tp.derivedLambdaType(resType = replaceResult(tp.resultType, restpe))
          case _ =>
            System.out.println(s"replaceResult._: $tp")
            restpe
        }
      }

      /** A method representing a hoisted supercall argument */
      def newSuperArgMethod(argType: Type) = {
        System.out.println(s"newSuperArgMethod : $argType")
        val (staticFlag, methOwner) =
          if (cls.owner.is(Package)) (JavaStatic, cls) else (EmptyFlags, cls.owner)
        System.out.println(s"staticFlag, methOwner: $staticFlag - $methOwner")
        val argTypeWrtConstr = argType.subst(origParams, allParamRefs(constr.info))
        System.out.println(s"argTypeWrtConstr : $argTypeWrtConstr")

        // argType with references to paramRefs of the primary constructor instead of
        // local parameter accessors
        val x = ctx.newSymbol(
          owner = methOwner,
          name = SuperArgName.fresh(cls.name.toTermName),
          flags = Synthetic | Private | Method | staticFlag,
          info = replaceResult(constr.info, argTypeWrtConstr),
          coord = constr.coord
        ).enteredAfter(thisPhase)
        System.out.println(s"ctx.newSymbol : ${x}")

        x
      }

      /** Type of a reference implies that it needs to be hoisted */
      def refNeedsHoist(tp: Type): Boolean = tp match {
        case tp: ThisType => !tp.cls.isStaticOwner && tp.cls != cls
        case tp: TermRef  => refNeedsHoist(tp.prefix)
        case _            => false
      }

      /** Super call argument is complex, needs to be hoisted */
      def needsHoist(tree: Tree) = tree match {
        case _: DefDef            => true
        case _: Template          => true
        case _: New               => !tree.tpe.typeSymbol.isStatic
        case _: RefTree | _: This => refNeedsHoist(tree.tpe)
        case _                    => false
      }

      System.out.println(s"hoist: $arg")
      // begin hoistSuperArg
      arg match {
        case Apply(fn, arg1 :: Nil) if fn.symbol == defn.cbnArg =>
          System.out.println(s"Apply(fn, ..): $fn, ${fn.symbol}")
          cpy.Apply(arg)(fn, hoistSuperArg(arg1, cdef) :: Nil)
        case _ if (arg.existsSubTree(needsHoist)) =>
          System.out.println(s"arg.existsSubTree(needsHoist)")
          val superMeth = newSuperArgMethod(arg.tpe)
          System.out.println(s"superMeth: $superMeth")
          val superArgDef = polyDefDef(superMeth, trefs => vrefss => {
            val paramSyms = trefs.map(_.typeSymbol) ::: vrefss.flatten.map(_.symbol)
            val tmap = new TreeTypeMap(
              typeMap = new TypeMap {
                lazy val origToParam = origParams.zip(paramSyms).toMap
                def apply(tp: Type) = tp match {
                  case tp: NamedType
                  if (tp.symbol.owner == cls || tp.symbol.owner == constr) &&
                     tp.symbol.isParamOrAccessor =>
                    System.out.println(s"apply(ty: Type): NamedType. $tp")

                    val t = origToParam.get(tp.symbol) match {
                      case Some(mappedSym) => if (tp.symbol.isType) mappedSym.typeRef else mappedSym.termRef
                      case None => mapOver(tp)
                    }
                    System.out.println(s"origToParam tp: Namedtype: $t")
                    t
                  case s =>
                    System.out.println(s"apply(ty: Type): _: $s")

                    val x = mapOver(tp)
                    System.out.println(s"mapOver: $x")
                    x
                }
              },
              treeMap = {
                case tree: RefTree if paramSyms.contains(tree.symbol) =>
                  System.out.println(s"treeMap is RefTree: $tree")
                  val a = cpy.Ident(tree)(tree.name).withType(tree.tpe)
                  System.out.println(s"cpy.Ident: $a")
                  a
                case tree =>
                  System.out.println(s"treeMap _: ${tree.show}")
                  tree
              })
            val x = tmap(arg).changeOwnerAfter(constr, superMeth, thisPhase)
            System.out.println(s"tmap(arg).changeOwnerAfter:  $x")
            x
          })
          superArgDefs += superArgDef
          System.out.println(s"superArgDefs: $superArgDefs")
          def termParamRefs(tp: Type, params: List[Symbol]): List[List[Tree]] = tp match {
            case tp: PolyType =>
              termParamRefs(tp.resultType, params)
            case tp: MethodType =>
              val (thisParams, otherParams) = params.splitAt(tp.paramNames.length)
              thisParams.map(ref) :: termParamRefs(tp.resultType, otherParams)
            case _ =>
              Nil
          }
          val (typeParams, termParams) = origParams.span(_.isType)
          System.out.println(s"typeParams: $typeParams")
          System.out.println(s"termParams: $termParams")
          val res = ref(superMeth)
            .appliedToTypes(typeParams.map(_.typeRef))
            .appliedToArgss(termParamRefs(constr.info, termParams))
          ctx.log(i"hoist $arg, cls = $cls = $res")
          System.out.println(i"hoist $arg, cls = $cls = $res")

          res
        case _ =>
          System.out.println(s"anything matched else: $arg")
          arg
      }
    }

    /** Hoist complex arguments in super call out of the class. */
    def hoistSuperArgsFromCall(superCall: Tree, cdef: DefDef): Tree = superCall match {
      case Apply(fn, args) =>
        System.out.println(s"hoistSuperArgsFromCall: $superCall and defdef $cdef")
        cpy.Apply(superCall)(hoistSuperArgsFromCall(fn, cdef), args.mapconserve(hoistSuperArg(_, cdef)))
      case _ =>
        superCall
    }

    /** Hoist complex arguments in this-constructor call of secondary constructor out of the class. */
    def hoistSuperArgsFromConstr(stat: Tree): Tree = stat match {
      case stat: DefDef if stat.symbol.isClassConstructor =>
        System.out.println(s"hoistSuperArgsFromConstr.DefDef: $stat")
        cpy.DefDef(stat)(rhs =
          stat.rhs match {
            case t@Block(superCall :: stats, expr) =>
              System.out.println(s"hoistSuperArgsFromConstr.DefDef.rhs.Block: $t")
              val superCall1 = hoistSuperArgsFromCall(superCall, stat)
              if (superCall1 eq superCall) {
                System.out.println(s"superCall1 eq superCall: ${stat.rhs}")

                stat.rhs
              }
              else {
                val x = cpy.Block(stat.rhs)(superCall1 :: stats, expr)
                System.out.println(s"else cpy.Block: $x")
                x
              }
            case _ =>
              hoistSuperArgsFromCall(stat.rhs, stat)
          })
      case _ =>
        System.out.println(s"hoistSuperArgsFromConstr._: $stat")
        stat
    }
  }

  override def transformTypeDef(tdef: TypeDef)(implicit ctx: Context): Tree = {
    System.out.println(s"transformTypeDef: ${tdef.show}")
    tdef.rhs match {
      case impl @ Template(cdef, superCall :: others, _, _) =>
        System.out.println(s"transformTypeDef.rhs:Template: ${impl.show}")
        val hoist = new Hoister(tdef.symbol)
        val hoistedSuperCall = hoist.hoistSuperArgsFromCall(superCall, cdef)
        val hoistedBody = impl.body.mapconserve(hoist.hoistSuperArgsFromConstr)
        if (hoist.superArgDefs.isEmpty) {
          System.out.println(s"hoist.superArgDefs.isEmpty: $tdef")
          tdef
        }
        else {
          val (staticSuperArgDefs, enclSuperArgDefs) =
            hoist.superArgDefs.toList.partition(_.symbol.is(JavaStatic))
          System.out.println(s"val (staticSuperArgDefs, enclSuperArgDefs): $staticSuperArgDefs, $enclSuperArgDefs")

          val f = flatTree(
              cpy.TypeDef(tdef)(
                  rhs = cpy.Template(impl)(
                      parents = hoistedSuperCall :: others,
                      body = hoistedBody ++ staticSuperArgDefs)) ::
              enclSuperArgDefs)
          System.out.println(s"flatTree: $f")
          f
        }
      case _ =>
        System.out.println(s"transformTypeDef.rhs:_: $tdef")
        tdef
    }
  }
}
