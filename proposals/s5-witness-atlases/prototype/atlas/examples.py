"""Small exact problems whose intended outcomes have hand proofs in the article."""
from .producer import problem,x,y


def examples():
    # (problem, expected closed truth; None means a free-parameter truth atlas)
    return [
      (problem('algebraic_positive', [y*y-x*x-1,y], ['and',['eq',0],['ge',1]]), True),
      (problem('square_root_conditional',[x,y*y-x,y],['implies',['ge',0],['and',['eq',1],['ge',2]]]), True),
      (problem('square_root_unconditional',[y*y-x],['eq',0]), False),
      (problem('strict_square_band',[x,y*y-x,y*y-x-1],['implies',['ge',0],['and',['gt',1],['lt',2]]]),True),
      (problem('inverse_hole',[x*y-1],['eq',0]),False),
      (problem('inverse_guarded',[x,x*y-1],['implies',['ne',0],['eq',1]]),True),
      (problem('vanishing_content',[x*(y*y-2),y],['and',['eq',0],['gt',1]]),True),
      (problem('two_shifted_squares',[y*y-2,(y-x)**2-2],['and',['eq',0],['eq',1]],outer='free'),None),
      (problem('overlapping_intervals',[y*y-x,(y-2)**2-x],['and',['le',0],['le',1]],outer='free'),None),
      (problem('uniform_positive_quadratic',[y*y+x*y+1],['gt',0],outer='free',inner='forall'),None),
      (problem('choose_positive_quadratic',[y*y+x*y+1],['gt',0],outer='exists',inner='forall'),True),
      (problem('surjective_cubic',[y**3-y-x],['eq',0]),True),
      (problem('surjective_quintic',[y**5+y-x],['eq',0]),True),
      (problem('repeated_zero_curve',[(y*y-x)**2],['ge',0],inner='forall'),True),
      (problem('strict_repeated_zero_curve',[(y-x)**2],['gt',0],inner='forall'),False),
      (problem('negative_algebraic_obstruction',[x*x-2,y*y-x,y],['implies',['eq',0],['and',['eq',1],['gt',2]]]),False),
      (problem('quantifier_order_forall_exists',[y-x],['gt',0]),True),
      (problem('quantifier_order_exists_forall',[y-x],['gt',0],outer='exists',inner='forall'),False),
      (problem('discontinuous_choice',[y*y-x*x-1,x,y-1,y+1],['and',['eq',0],['implies',['ge',1],['ge',2]],['implies',['lt',1],['le',3]]]),True),
      (problem('empty_and_constant_atoms',[0,1,-1],['and',['eq',0],['gt',1],['lt',2]]),True),
      (problem('constant_false',[0],['ne',0],outer='exists',inner='exists'),False),
      (problem('degree_drop_at_zero',[x*y*y+y-1],['eq',0],outer='free'),None),
      (problem('strict_and_disequality',[y*y-x,y],['and',['eq',0],['ne',1]],outer='free'),None),
      (problem('algebraic_section_only',[x*x-2,y-x],['and',['eq',0],['eq',1]],outer='exists'),True),
    ]
