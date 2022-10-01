import { StreamLanguage, StreamParser, StringStream } from '@codemirror/stream-parser';
import { defaultHighlightStyle, classHighlightStyle }  from '@codemirror/highlight';


class SuslikSyntaxHighlighting implements StreamParser<{}> {

    rules: {start: {token: string | ((t: string) => string), regex: RegExp}[]}
    token: (stream: StringStream, state: {}) => string

    constructor() {
        this.rules = SuslikSyntaxHighlighting.rules();

        this.token = (stream: StringStream, state: {}) => {
            for (let {token, regex} of this.rules.start) {
                let mo = stream.match(regex);
                if (mo)
                    return (typeof token === 'function') ? token(mo[0]) : token;
            }

            stream.next();
            return null;
        }
    }
}

namespace SuslikSyntaxHighlighting {

    export function rules() {
        var keywords =
            ("if|else|true|false|emp|not|predicate|in").split("|");
    
        var builtInTypes =
            ("bool|int|loc|set|void").split("|");
    
        var operators =
          ("+|-|==|!=|<|<=|>|>=|&&|\|\||=>==>|**|:->|?|:|,|\||;").split("|");
    
        // regexp must not have capturing parentheses. Use (?:) instead.
        // regexps are ordered -> the first match is used
    
        return {
            "start" : [
                {
                    token : 'comment',
                    regex : /\/\/.*$/
                },
                {
                    token : 'bool',
                    regex : /(?:true|false|e)\b/
                },
                {
                    token : function(value) {
                        if (keywords.includes(value))
                            return 'keyword';
                        else if (builtInTypes.includes(value))
                            return 'typeName';
                        else
                            return 'variableName';
                    },
                    regex : /[a-zA-Z_'$][a-zA-Z0-9_'$]*\b/
                },
                {
                    token : 'operator',
                    regex : /\*\*|\+|-|==|!=|<|<=|>|>=|&&|\|\||=>|==>|:->|:|\?\??/
                },
                {
                    token : 'paren',
                    regex : /[[({]/
                },
                {
                    token : 'paren',
                    regex : /[\])}]/
                },
                {
                    token : null,
                    regex : /\s+/
                }
            ],
        };
    };    
}

const parser = new SuslikSyntaxHighlighting();

export const suslikLanguage = [
    StreamLanguage.define(parser),
    defaultHighlightStyle,
    classHighlightStyle
];