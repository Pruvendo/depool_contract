# Requires jsbeautifier
# pip install jsbeautifier wasabi

import re, argparse, difflib
from typing import List, Tuple, Union, Set
import sys, jsbeautifier, os.path, traceback
from collections.abc import Iterable 

try:
    from wasabi import color
except ImportError:
    color = None

RX_ID = r'[a-zA-ZА-Яа-я\'_α-ωΑ-Ω][a-zA-ZА-Яа-я0-9_\'α-ωΑ-Ω]*'
RX_BALANCED_BOUNDS = r'(?:[^)(]|\((?:[^)(]|\([^)(]*\))*\))*'
RX_COMMENT =          r'\(\*(\(\*((?!\*\)).|\n)*\*\)|((?!\*\)|\(\*).|\n)*)*\*\)'
RX_COMMENT_REVERSED = r'\)\*(\)\*((?!\*\().|\n)*\*\(|((?!\*\(|\)\*).|\n)*)*\*\('
RX_DEF_NAME = rf'Definition\s+({RX_ID})'
COLORED_TERMINAL = True

class SubPattern:
    def __init__(self, pattern: str, repl: str, line_num: int):
        self.pattern = pattern
        self.repl = repl
        self.line_num = line_num

def remove_comments(s: str):
    # single level of comment nesting (* aaa (* aaa *) *)
    return re.sub(RX_COMMENT, '', s)

# based on https://gist.github.com/ines/04b47597eb9d011ade5e77a068389521
def diff_strings(a, b, colored=True):
    output = []
    matcher = difflib.SequenceMatcher(None, a, b)
    # TODO: it's very slow even in short files, quadratic complexity at best, cubic on average
    if not COLORED_TERMINAL or not colored or color is None:
        return ''.join(difflib.ndiff(a.splitlines(keepends=True), b.splitlines(keepends=True)))
    
    for opcode, a0, a1, b0, b1 in matcher.get_opcodes():
        if opcode == "equal":
            output.append(a[a0:a1])
        elif opcode == "insert":
            output.append(color(b[b0:b1], fg=16, bg="green"))
        elif opcode == "delete":
            output.append(color(a[a0:a1], fg=16, bg="red"))
        elif opcode == "replace":
            output.append(color(b[b0:b1], fg=16, bg="green"))
            output.append(color(a[a0:a1], fg=16, bg="red"))
    return "".join(output)

def process_definition(text: str, show_progress=Union[bool, List[str]]) -> Tuple[str, List[SubPattern], Set[str]]:
    active_patterns = set()
    used_patterns = list()
    show_all_progress = isinstance(show_progress, bool) and show_progress
    patterns_to_show = set(show_progress) if isinstance(show_progress, Iterable) else set()

    def upd(new_text: str, comment: str, show_diff: bool):
        nonlocal text, show_progress
        if new_text != text:
            if show_diff:
                print(comment)
                if len(re.findall(r'\(', new_text)) - len(re.findall(r'\)', new_text)) != \
                   len(re.findall(r'\(', text)) - len(re.findall(r'\)', text)):
                   print('UNBALANCED BRACKETS')
                sys.stdout.writelines(diff_strings(text, new_text))
            text = new_text
            return True
        else:
            return False

    def sub(pattern: str, repl: str):
        nonlocal text

        show_diff = show_all_progress or pattern in patterns_to_show
        line_num = None
        for frame_type, frame_line in traceback.walk_stack(None):
             if frame_type.f_code.co_name == 'process_definition':
                line_num = frame_line
                break
        show_diff = show_diff or line_num and str(line_num) in patterns_to_show
        changed = upd(re.sub(pattern, repl, text, flags=re.MULTILINE), f'\n\nPATTERN = {pattern} -> {repl}', show_diff=show_diff)
        used_patterns.append(SubPattern(pattern, repl, line_num))
        if changed:
            active_patterns.add(pattern)
        return changed

    def sub_repeatedly(patterns: List[Tuple[str, str]]):
        while True:
            changed = False
            for (pattern, repl) in patterns:
                changed = sub(pattern, repl) or changed
            if not changed:
                break

    def brk():
        nonlocal show_all_progress, patterns_to_show
        if show_all_progress or len(patterns_to_show) > 0:
            show_all_progress = False
            patterns_to_show = set()
            print('\n------------------------')
            print(text)

    text = remove_comments(text)

    sub(r'↑ε[0-9]*', '')
    sub(r'\bε\b', '')
    sub(r'U[0-9]!', '')
    sub(r'D[0-9]!', '')
    sub(r'↑+[0-9]+', '')   
    sub(r'ς\s+return#.*?\.', r'.')
    
    sub(r'\(\s*ξ\$\s+(?:[A-Za-z0-9_]+?_ι_)?([_A-Za-z0-9]*?)P?_ι_([_A-Za-z0-9]*?)\s\)', r'\1__DOT__\2')
    sub(r'ξ(?:\s*\$)?\s+(?:[A-Za-z0-9_]+?_ι_)?([_A-Za-z0-9]*?)P?_ι_([_A-Za-z0-9]*?)', r'\1__DOT__\2')

    sub(r'^\s*initial.*?>>', '')
    sub(r'\(\s*LocalState_ι_[_A-Za-z0-9]*?_Л_([_A-Za-z0-9]*?)\s*:=\s*\$\s*Л_\1\s*\)', r'') # removes initialisation of pseudolocals
    sub(r'LocalState_ι_.*?_Л_(.*?)\b', r'\1')
    sub(r'\:\s*[A-Za-z0-9_]+?_ι_([A-Za-z0-9_]+?)', r': \1')  
    sub(r'([A-Za-z0-9]+_И_[A-Za-z0-9]+)F', r'\1')
    sub(r'[A-Za-z0-9_]+_ι_([A-Za-z0-9_]+?)P?_ι_([A-Za-z0-9_]+?)\b', r'\2')
    sub(r'(?:(?!__DOT__)[A-Za-z0-9_])+_ι_([A-Za-z0-9_]+?)', r'\1')

    # declarations of variables. declareLocal/Global/Init. declareInit removes 
    sub(r'declareLocal\s+([a-zA-ZА-Яа-я\'_α-ωΑ-Ω][a-zA-ZА-Яа-я0-9_\'α-ωΑ-Ω]*)\s*:>:\s*([A-Za-z0-9_]+)\s+:=\s*{\|\|((?:.|\n)*?)\|\|} ;',
         r'\2 \1 = \2 ( { \3 __RCURLY__ ) __SEMICOLON__')
    sub(r'declareLocal\s+(?!{\()(.*?)\s*(?:\:>\:|::::)\s*\(?(.*?)\)?\s*\?*:=', r'\2 \1 =')
    sub(r'declareLocal\s+({\(.*?\)})\s*\?*:=', r'\1 =')
    sub(rf'declareLocal\s+({RX_ID})', r'\1')
    sub(r'\(\s*declareGlobal\!?\s+(?!{\()(.*?)\s*\:>\:\s*\((.*?)\)\s*:=((.|\n)*?)\)\s*>>', r'\2 \1 = \3;')
    sub(r'\(\s*declareGlobal\!?\s+(?!{\()(.*?)\s*\:>\:\s*(.*?):=((.|\n)*?)\)\s*>>', r'\2 \1 = \3;')
    sub(rf'declareGlobal\s+({RX_ID})', r'\1')
    sub(r'\(.*?declareInit.*? >>', r'')
    sub('(' + RX_ID + r')\s*(?:\:>\:|::::)\s*(\([A-Za-z0-9 ]+\)|(?:(?!\)\})[^,;)])*)', r'\2 \1')

    sub(r'XHMap ([a-zA-Z0-9ι_]*) ([a-zA-Z0-9ι_]*)', r'mapping (\1 => \2)')
    sub(r'XList\s+XInteger8', 'bytes')
    sub(rf'XMaybe\s+\(({RX_ID})\)', r'optional(\1)')
    sub(rf'XMaybe\s+({RX_ID})', r'optional(\1)')
    sub(rf'XMaybe', r'optional')
    sub(r'do(?:\s*_)\s*←\s*\(\s*ForIndexedE\s*\(\s*xListCons\s+(.*?)\s*\(xListCons\s+xInt1\s*xListNil\s*\)\s*\)'
        r'\s+do\s*\(\s*fun\s+\((.*?):\s+(.*?)\)\s+=>',
        r'for ( \3 \2 = \1; \2 < 2; ++ \2) {')
    
    sub(r'\) >>= fun r => return! \(xProdSnd r\) \) \?\?;', '} __SEMICOLON__')
    sub(r'\(\s*ForIndexed\s*\(\s*xListCons\s+(.*?)\(xListCons\s+xInt1\s*xListNil\s*\)\s*\)\s+do\s*\(\s*fun\s+\((.*?):\s+(.*?)\)\s+=>',
        r'for ( \3 \2 = \1; \2 < 2; ++ \2) {')
    sub(rf'\(\s*({RX_ID})\s*:\s*(optional\s*\(\s*{RX_ID}\s*\)|mapping\s*\(\s*{RX_ID}\s*=>\s*{RX_ID}\s*\)|{RX_ID})\s*\)', r'\2 \1, ')
    sub(r'XInteger', 'uint')
    sub(r'XBool', 'bool')
    sub(r'XAddress', 'address')
    sub(r'\(\s*xValue\s+I\s*\)', '')
    sub(r'[Xx]Value\s+I', '')
    sub(r'XValueValue', '')
    sub(r'XArray\s+([A-Za-z0-9]+)', r'\1[]')
    sub(r'::=', ':')

    sub(r'Definition\s+([_a-zA-Z0-9Ф]*_[Cc]onstructor[0-9]+) ((?:.|\n)*),\s+:\s+.*?:= (?:\s|\n)*New ([A-Za-z0-9]+)[_ФA-Za-z0-9]+ (.*?) >>',
        r'constructor (\2) \3 \4 {')
    sub(r'Definition\s+([_a-zA-Z0-9Ф]*_[Cc]onstructor[0-9]+)', r'constructor (')
    sub(r'Definition\s+([_a-zA-Z0-9Ф]*)\'?', r'function \1 (')
    sub(r'\.', ';}')
    sub(r',\s*:', ':')
    sub(r'\s*:\s*LedgerT(.*):=(?:\s|\n)*returns\s+(.*)>>', r') returns \2 {') # it will break if applied to the entire file instead of definitions
    sub(r'LedgerT\s+([A-Za-z0-9]+)\s*:=', r'LedgerT (\1) :=')
    sub(r':\s*LedgerT', ') returns')
    sub(r'\s*XErrorValue(.*)uint\s*\)', r' \1 )')
    sub(r'return#', 'return')
    sub(r'#', ',')
    sub(r'(_Ф_[A-Za-z0-9_]+)\s+;\s+\$I\b', r'\1 ( ) ;')
    sub(r'function ((?:.|\n)*)returns ((?:[^{]|\n)*?):=', r'function \1 returns \2 {')
    sub(r'\bTrue\b', '')
    sub(r'xBool(True|False)', r'\1')
    sub(r'True', r'true')
    sub(r'False', r'false')
    sub(r'xInt([a-z0-9_]*)', r'\1')
    sub(r'[a-zA-Z0-9_]*Ф_([a-zA-Z0-9_]*)', r'\1')    
    sub(r':=\s+\$default', '')
    sub(r'xError\s*\(', '(')
    sub(r'(?<!{)\$\s*I\b', '')
    sub(r'(?<!{)\$(?!})', '')
    sub(r'Require2? {{\$?\s*((.|\n)*?)\s*}}', r'require ( \1 )')

    sub(r'->store\s+(.+?)\s+([^\s;]+)', r'.store(\1, \2)') # the function is problematic, because it doesn't use parentnesses, better to change the notation

    # tvm
    sub(r'tvm_address\s*\(\s*\)', 'address ( this )')
    sub(r'tvm_now\s*\(\s*\)', r'now')
    sub(r'tvm_rawConfigParam_([0-9]+)(\s*\(\s*\))?', r'tvm.rawConfigParam(\1)')
    sub(r'tvm_configParam_([0-9]+)(\s*\(\s*\))?', r'tvm.configParam(\1)')
    sub(r'\(\s*tvm_functionId (.*?)F?\s*\)', r'tvm_functionId(\1)')
    sub(r'tvm_revert', r'revert')
    sub(r'tvm_exit\s*\(\s*\)', r'tvm.exit();')
    sub(r'tvm_balance\s*\(\s*\)', r'address(this).balance')
    sub(r'tvm_([a-zA-Z]+)', r'tvm.\1')

    sub(r'>>=[\s\n]+fun[\s\n]+x[\s\n]+=>[\s\n]+return![\s\n]+\(\s+xError[\s\n]+x\s*\)', ';')
    
    # send message
    sub(r'with\s+messageValue', r'with value')
    sub(r'with\s+([a-zA-Z0-9]+)\s*:=', r', \1 : ')
    sub(r'\bmessageValue\b', 'value')
    sub(r'\bmessageBounce\b', 'bounce')
    sub(r'\bmessageFlag\b', 'flag')

    sub(r'this->sendMessage\s*'
        r'\(.*?(?:И_)?([A-Za-z0-9_]*?)F?\s+\(\!\!((?:.|\n)*?)\!\!\)\s*\)\s*with\s*\{\|\|((.|\n)*?)\|\|\}',
        r'this.\1{\3 __RCURLY__ (\2)')    
    sub(r'this->sendMessage\s*'
        r'\(.*?(?:И_)?([A-Za-z0-9_]*?)F?\s+\s*\)\s*with\s*\{\|\|((.|\n)*?)\|\|\}',
        r'this.\1{\2 __RCURLY__ ()')

    sub(r'(?:\"(.*?)\"|([A-Za-z0-9]+))\s+of\s+\(\s*(.*?)\)\s+->sendMessage\s*'
        r'\(.*?(?:И_)?([A-Za-z0-9_]*?)F?\s+\(\!\!((?:.|\n)*?)\!\!\)\s*\)[\s\n]*with\s*\{\|\|((?:.|\n)*?)\|\|\}',
        r'\1\2(\3).\4{\6 __RCURLY__ (\5)')

    # Some statements
    sub(r'(?<![A-Za-z_9])If2?!*', r'if ')
    sub(r'then', r'')
    sub(rf'({RX_ID})\s*:=\s*default\s*,', r'')
    sub(rf'({RX_ID})\s*:=\s*default\s*', r'')
    sub(r'\?\?:=', r'=')
    sub(r'_\s+\?:=', r'')
    sub(r':=', r'=')

    sub(r'\b_\b', '')
    sub(r'Л_', '')

    sub(r'\s0\s+!-', ' !-')

    # Operators
    sub(r'\?([!<>=]+)', r'\1')
    sub(r'!([+\-*/%])', r'\1')
    sub(r'!¬', r'!')
    sub(r'!&', r'&&')
    sub(r'!\|', r'||')
    sub(r':::', r':')
    sub(r'\[\[', r'[')
    sub(r'\]\]', r']')
    sub(r'\[\(', r'(')
    sub(r'\)\]', r')')
    sub(r'\{\(', r'(')
    sub(r'\)\}', r')') 
    sub(r'\^\^', r'.')

    sub(r'->min(?![0-9])', '.min()')
    sub(r'math->min[0-9]+', 'math.min')
    sub(r'math->max[0-9]+', 'math.max')

    sub(r'\(\s*if\b', r'if')
    sub(r'^\s*\((?![!])\)', r'')
    sub(r'(?<!})}\s*\)', r'; }')
    sub(r'->set\s*([A-Za-z0-9]+\))', r'->set (\1')
    sub(r'->toCell', r'.toCell()')
    sub(r'->set', r'.set')
    sub(r'\(\s*->emit ((.|\n)*?)\)(\s|\n)*(;|>>)', r'->emit \1;')
    sub(r'->emit\s*\(((.|\n)*?)\)\s*;', r'->emit \1;')
    sub(r'->emit', r'emit')
    sub(r'->selfdestruct', r'selfdestruct')
    sub(rf'->(fetch|next|exists|delete|push)\s+({RX_ID})', r'.\1(\2)')
    sub(r'->(get|hasValue|empty|reset)', r'.\1()')
    sub(r'->>?', r'.')
    sub(r'\bDePoolClosed', 'DePoolClosed()')
    
    # sub(r'DePoolLib__DOT__RequestC queryId validatorKey stakeAt maxFactor adnlAddr signature')
    sub(r'DePoolLib__DOT__RequestC((\s+[a-zA-Z0-9]+)*)', r'Request( \1 __ENDREQUEST__')
    sub(r'(?=([A-Za-z ]+)__ENDREQUEST__)([A-Za-z]+)', r'\2, ')
    sub(r',\s*__ENDREQUEST__', r')')

    sub(r'msg_sender\s*\(\s*\)', 'msg.sender')
    sub(r'msg_value\s*\(\s*\)', 'msg.value')
    sub(r'msg_value', 'msg.value')
    sub(r'msg_pubkey\s*\(\s*\)', 'msg.pubkey ()')

    sub(r'\s*\(\s*optional\s*\(([A-Za-z0-9]+)\)\s*\)(?!\s*{)', r'optional(\1)')

    sub(r'>>=(.|\n)*\?;', r';')

    sub(r'\(+\s*While ((.|\n)*?)\s+do(\s|\n)+\(', r'while \1 {')
    sub(r'do\s+←\s*\(\s*WhileE\s+((?:.|\n)*?)\s+do', r'while \1 {') # todo: whileE
    sub(r'continue!(\s+I)?', '')
    sub(r'^\s*(\)\s*)+>>', ';}')
    sub(r'>>', r';')

    # Преобразуем {|| A := B, C := D, ... ||} в { A: B, C: D }
    sub(r'{\|\|', '{')
    sub(r'\|\|}', '__RCURLY__')
    sub(r'returns\s*\(\s*\(\s*\((.*?)\)\s*\)\s*\)', r'returns (\1)')
    sub(r'returns\s*\(\s*\((.*?)\)\s*\)', r'returns (\1)')

    # Постфиксные функции в префиксной нотации. Лучше поменять нотацию
    sub(r'\(\s*delMin(.*?)\)', r'\1.delMin().get()')

    sub(r'completionReason2uint', r'uint8')
    sub(r'emit\s+round', r'emit Round')

    sub(r'\breturns(\s*\(\s*\))?\s*[{=]', '{')
    sub(r'_ι_', r'.')
    sub(r'_И_', r'.')
    sub(r'return!{1,3}', r'return')
    sub(r'return\s+I', 'return')
    sub(r'}', r'; }')
    sub_repeatedly([(r';\s*;', ';')])
    sub(r'DePoolContract.', '')
    sub(r'\(!+', '(')
    sub(r'!+\)', ')')
    sub(r'}\s*;', '}')
    sub(r'(xError false)', 'false')
    sub(r'([0-9]+)\s*\*\s*x1_day', r'(\1 days)')
    sub(r'=\s*default', r'')

    # regexp specifically to remove parentnesses after if in in onBounce
    sub(r'(if\s+\(\s*(isRound[0-9]\s*\(\s*roundId\s*\)|isProcessNewStake)\s*\)\s*{\s*)\(', r'\1')

    # delete inside of brackets doesn't work in Solidity, we have to remove them
    sub(r'\(\s*delete\s+([a-zA-Z0-9_\[\]\.\n ]+)\)', r'delete \1')

    # cosmetics, remove some unnecessary brackets
    sub(r'(?<![A-Za-z0-9_ \t])\s*\(\s*([A-Za-z0-9_]+(\s*\.\s*[A-Za-z0-9_]+)*)\s*\)\s*', r'\1 ')
    sub(r'{\s*(;\s*)+}', '{ }')

    sub(r'__DOT__', '.')
    sub(r'__RCURLY__', '}')
    sub(r'__SEMICOLON__', ';')
    sub(r'\(\s*xError\s+I\s*\)', r'')

    return text, used_patterns, active_patterns

def split_text_into_definitions(text: str):
    text_no_comments = remove_comments(text)
    text_reversed = text[::-1]
    for m in re.findall(r'(Definition (.|\n)*?\.)', text_no_comments):
        # ignore definitions like "Definition DePoolProxyContract_Ф_process_new_stake := DePoolProxyContract_Ф_process_new_stake .", etc.
        if re.match(r'Definition ([A-Za-zФ_0-9]+) := \1 \.', m[0]):
            continue
        name = re.search(RX_DEF_NAME, m[0])[1]
        # Прямой регексп виснет, поэтому ищем по перевернутому тексту
        pattern_for_last_comment = r'{0}\s+{1}\s+({2})'.format(name[::-1], 'Definition'[::-1], RX_COMMENT_REVERSED)
        m_last_comment = re.search(pattern_for_last_comment, text_reversed)
        last_comment = m_last_comment[1][::-1][3:-2] if m_last_comment else None
        yield m[0], name, last_comment

def process_file(input_path: str):
    with open(input_path) as f:
        text = f.read()
        def_matches = list(split_text_into_definitions(text))
        all_defs = [name for _, name, _ in def_matches]
        for def_text, def_name, def_comment in def_matches:
            sol_text, used_patterns, active_patterns = process_definition(def_text, False)
            yield all_defs, def_name, def_text, def_comment, sol_text, used_patterns, active_patterns

def beautify(sol_text: str, for_diff=False) -> str:
    sol_text = jsbeautifier.beautify(sol_text)
    sol_text = re.sub(r'\n+', r'\n', sol_text)
    if for_diff:
        sol_text = re.sub(r'([,\+=/]|&&|\|\||return)(\s|\n)+', r'\1 ', sol_text)
        sol_text = re.sub(r'([\(\.])(\s|\n)+', r'\1', sol_text)
        sol_text = re.sub(r'(\s|\n)+;', r';', sol_text)
        sol_text = re.sub(r'^\s+', r'', sol_text, flags=re.MULTILINE)
        sol_text = re.sub(r'(\s|\n)+([\)\.])', r'\2', sol_text)
        sol_text = re.sub(r'\)(\s|\n)+{', r') {', sol_text)
    return sol_text

def generate_def_files(input_path: str, output_directory: str, refs_directory: str):
    all_used_patterns = set([pattern.pattern for pattern in process_definition('', False)[1]])
    all_active_patterns = set()
    for all_defs, name, def_text, def_comment, sol_text, _, active_patterns in process_file(input_path):
        outpath = os.path.join(output_directory, name)
        if (name + '\'') in all_defs or '_Ф_' not in name:
            pass
        else:
            all_active_patterns.update(active_patterns)
            if refs_directory and os.path.exists(os.path.join(refs_directory, name)):
                with open(os.path.join(refs_directory, name)) as f:
                    def_comment = f.read()
            with open(outpath, 'w', encoding='utf-8') as f:
                f.write(def_text)
                f.write('\n===== TRANSLATED =====\n')
                f.write(beautify(sol_text))
                f.write('\n===== REFERENCE =====\n')
                def_comment = def_comment or ''
                f.write(def_comment)
                f.write('\n===== DIFF =====\n')
                f.write(diff_strings(beautify(sol_text, for_diff=True), beautify(def_comment, for_diff=True), colored=False))
    dead_patterns = all_used_patterns.difference(all_active_patterns)
    print('DEAD PATTERNS: ', sorted(dead_patterns))

def find_dead_patterns(input_path: str):
    all_used_patterns = set([pattern.pattern for pattern in process_definition('', False)[1]])
    all_active_patterns = set()
    for all_defs, name, def_text, def_comment, sol_text, used_patterns, active_patterns in process_file(input_path):
        outpath = os.path.join(output_directory, name)
        all_active_patterns.update(active_patterns)
    dead_patterns = all_used_patterns.difference(all_active_patterns)
    return dead_patterns

def explain_definition(input_path: str, name_def: str):
    for all_defs, name, def_text, _, sol_text, _, _ in process_file(input_path):
        if name == name_def:
            process_definition(def_text, True)

def pattern_examples(input_path: str, pattern_examples: List[str]):
    pattern_stats_by_pattern = {}
    pattern_stats_by_line = {}
    all_patterns_table = None

    for all_defs, name, def_text, _, sol_text, _, _ in process_file(input_path):
        _, used_patterns, active_patterns = process_definition(def_text, show_progress=pattern_examples)
        all_patterns_table = all_patterns_table or {ptrn.pattern: ptrn for ptrn in used_patterns}
        for pattern in active_patterns:
            pattern_stats_by_pattern[pattern] = pattern_stats_by_pattern.get(pattern, 0) + 1
            line_num = str(all_patterns_table[pattern].line_num)
            pattern_stats_by_line[line_num] = pattern_stats_by_line.get(line_num, 0) + 1

    print('\nPATTERN USAGE')
    for k in pattern_examples:
        print ('{:<21} {:<} time(s)'.format(k[:20], pattern_stats_by_pattern.get(k, pattern_stats_by_line.get(k, 0))))

def print_all_patterns(input_path: str, exclude_dead=True, print_as_python=False):
    dead_patterns = find_dead_patterns(input_path)
    all_patterns = process_definition('', False)[1]
    i = 1

    if print_as_python:
        print('import re\n\ndef translate_definition(text: str) -> str:')

    for pattern in all_patterns:
        if pattern.pattern not in dead_patterns:
            if print_as_python:
                print(f'\ttext = re.sub(r\'{pattern.pattern}\', r\'{pattern.repl}\', text, flags=re.MULTILINE)')
            else:
                print(f'{i}\'. {pattern.pattern} --> {pattern.repl}')
            i += 1

    if print_as_python:
        print('\treturn text')

if __name__ == "__main__":
    output_directory = '.'
    input_path = None
    reference_directory = None
    
    parser = argparse.ArgumentParser()
    parser.add_argument('--explain', dest='explain', help='Shows step by step application of regexps for selected definition')
    parser.add_argument('--example', dest='pattern_examples', nargs='+', action='store', help='Shows transforms with selected regexp, for example :::')
    parser.add_argument('--print-all-patterns', dest='print_all_patterns', action='store_true', help='Print all alive patterns')
    parser.add_argument('--print-as-python', dest='print_as_python', action='store_true', help='Print all patterns in python code')
    parser.add_argument('--input', dest='input_path', required=True, help='Path to DePoolFunc.v file')
    parser.add_argument('--target-path', dest='output_directory', help='Path to directory to place generated files')
    parser.add_argument('--refs-path', dest='reference_directory', help='Directory for reference files')
    args = parser.parse_args()
    input_path = args.input_path or input_path
    output_directory = args.output_directory or output_directory
    reference_directory = args.reference_directory or reference_directory
    if args.print_all_patterns or args.print_as_python:
        print_all_patterns(input_path, print_as_python=args.print_as_python)
    elif args.pattern_examples:
        pattern_examples(input_path, args.pattern_examples)
    elif args.explain:
        explain_definition(input_path, args.explain)
    else:
        generate_def_files(input_path, output_directory, reference_directory)
