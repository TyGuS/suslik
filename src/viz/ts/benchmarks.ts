

class BenchmarksDB {
    data: BenchmarksDB.Data

    constructor(data: BenchmarksDB.Data) {
        this.data = data;
    }

    getSpec(dir: string, fn: string): BenchmarksDB.Data.Spec {
        return {
            name: `${dir}:${fn}`, 
            spec: {
                defs: this.getDefs(dir),
                ...this.getInputSpec(dir, fn)
            }
        };
    }

    getDefs(dir: string) {
        return Object.entries(this.data[dir])
            .map(([fn, txt]) => fn.endsWith('.def') && txt).filter(x => x);
    }

    getInputSpec(dir: string, fn: string) {
        var prog = this.data[dir][fn];
        return {...BenchmarksDB.Data.parseInputSpec(prog),
                config: {inputFormat: this.getFormat(fn)}};
    }

    getFormat(fn: string): [string] {
        return fn.endsWith('.syn') ? ['syn'] :
               fn.endsWith('.sus') ? ['sus'] :
               undefined;
    }

    static async load(url = './benchmarks.db.json') {
        return new BenchmarksDB(await (await fetch(url)).json());
    }
}

namespace BenchmarksDB {
    export type Data = {[dir: string]: {[fn: string]: string}};

    export namespace Data {
        export type Spec = {
            name?: string
            spec: {
                defs: string[]
                in: string
                config?: SpecConfig
            }
            params?: string[]
        }

        export type SpecConfig = {
            inputFormat?: [string]  /* contained in an array to serialize as Option[String] in Scala */
        }

        export function parseSpec(name: string, text: string): Spec {
            var inputSpec = parseInputSpec(text);
            return {name, spec: {defs: [], ...inputSpec}, params: inputSpec.params};
        }

        export function parseInputSpec(text: string) {
            var hashline = text.match(/^#[.]?(.*)\n([^]*)/),
                enclosure = text.match(/###+([^]*?)###+/),
                params = hashline?.[1].trim().split(/\s+/),
                in_ = enclosure?.[1] || hashline?.[2] || text;
            return {in: in_, params};
        }

        export function unparseSpec(spec: Spec) {
            var params = spec.params ? [`# ${spec.params.join(' ')}`] : [];
            return [...params, ...spec.spec.defs, spec.spec.in].join('\n');
        }
    }
}


export { BenchmarksDB }
