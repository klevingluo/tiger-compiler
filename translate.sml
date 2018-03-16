(* So from what I understand, this is the value environment compared to typenv's
 * type environment.  This is more complicated than the type environment because
 * values are mutable at run time.  They key thing that I think andrew is trying
 * to have us figure out is that the translate levels are created during
 * analysis and the frame levels are created during runtime.
 *
 * note:
 * This to me indicates that a level needs to have a parent and some set of
 * machine instructions for generating a new frame.
 *)
signature TRANSLATE =
sig
  type level
  type access (* not the same as Frame.access *)

  val outermost : level
  val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
  val formals : level -> access list
  val allocLocal : level -> bool -> access
end

structure Translate : TRANSLATE = 
struct 
  structure Frame : FRAME = MipsFrame
  type level = (int * Frame.frame)
  type access = (level * Frame.access) 

  (* this is the level that housees the program.  "library" functions are
   * declared at this level, which does not contain a frame, or parameter list
   *)
  val outermost = (0, frame=Frame.newFrame({name=Temp.newlabel(), formals=[]}))

  (* called during the translation of declarations *)
  val newLevel({(level , frame), name, formals}) =
    (level + 1,
     frame=Frame.newFrame({name=name, formals=true::formals}))

  (* called whenever a local variable is declared *)
  val allocLocal((lev, frame)) =
    fn esc =>
      ((lev, frame), Frame.allocLocal(frame)(esc))

  type exp = unit 
end
