"""Command-line solve/replay interface. Replay has no third-party dependency."""
from pathlib import Path
import argparse,json,sys
from .io import load
from .checker import verify,problem_polynomials
from .exact import LimitExceeded

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    check=sub.add_parser('verify',help='audit an existing certificate')
    check.add_argument('problem');check.add_argument('certificate')
    solve=sub.add_parser('solve',help='produce and audit an atlas (requires SymPy)')
    solve.add_argument('problem');solve.add_argument('--output',required=True)
    args=parser.parse_args()
    try:
        p=load(args.problem);problem_polynomials(p)
        if args.command=='verify':c=load(args.certificate)
        else:
            from .producer import produce
            c=produce(p)
        result=verify(p,c)
        if args.command=='solve':
            path=Path(args.output);path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(json.dumps(c,indent=2)+'\n',encoding='utf-8')
        print(json.dumps(result,indent=2));return 0
    except LimitExceeded as e:
        print(json.dumps({'status':'UNKNOWN','reason':str(e)}));return 2
    except (ValueError,ArithmeticError,TypeError,KeyError,IndexError,OSError,ImportError) as e:
        print(json.dumps({'status':'NO_ACCEPTED_CERTIFICATE','reason':str(e)}));return 1

if __name__=='__main__':sys.exit(main())
