import { EventEmitter } from 'events';
import $ from 'jquery';
import Vue from 'vue';

// @ts-ignore
import app from '../vue/app.vue';
import { BenchmarksDB } from './benchmarks';
import { ProofTrace } from './proof-trace';
import { ProofInteraction } from './proof-interaction';

import './ide.css';



class MainDocument extends EventEmitter {

    app: Vue
    pt: ProofTrace
    pi: ProofInteraction
    notifications: JQuery

    props: any

    storage: {'suslik:doc:lastUrl'?: string} = <any>localStorage;

    constructor(container: JQuery, notifications: JQuery) {
        super();
        this.app = new Vue(app).$mount();
        this.notifications = notifications;

        (<Vue>this.app.$refs.benchmarks).$on('action', ev => {
            this.emit('benchmarks:action', ev);
        });
    }

    get $el() { return this.app.$el; }

    new() {
        return this.setProofTrace(ProofTrace.Data.empty());
    }

    async open(content: string | File, opts: OpenOptions = {}): Promise<ProofTrace> {
        if (content instanceof File) {
            return this.open(await this.read(content), {name: content.name, ...opts});
        }
        else {
            try {
                return this.setProofTrace(ProofTrace.Data.parse(content));
            }
            catch (e) {
                if (!opts.silent) {
                    var msg = (e instanceof SyntaxError) ? 'JSON format error' : 'read error';
                    this.message(`Cannot open '${opts.name}': ${msg}`);
                }
            }
        }
    }

    async openUrl(url: string, opts?: OpenOptions) {
        var pt = await this.open(await (await fetch(url)).text(), opts)
        if (pt)
            this.storage['suslik:doc:lastUrl'] = url;
        return pt;
    }

    openRecent(opts?: OpenOptions) {
        return this.openUrl(this.storage['suslik:doc:lastUrl'] || DEFAULT_URL, opts);
    }

    setProofTrace(ptData: ProofTrace.Data) {
        this.pt?.destroy();
        this.pi?.destroy();

        var pt = new ProofTrace(ptData, this.app.$refs.proofTrace as any),
            pi = new ProofInteraction(pt);
        this.pt = pt;
        this.pi = pi;
        pt.on('expand', (nodeView: ProofTrace.View.Node) => {
            if (nodeView.value.tag == ProofTrace.Data.NodeType.OrNode &&
                nodeView.children.length == 0) {
                /* send request to server */
                if (this.pi) this.pi.sendExpandRequest(nodeView.value.id);
            }
        });
        pi.on('trace', u =>
            this.pt.append(ProofTrace.Data.fromEntries([u])));

        this.emit('open', pt);
        return pt;
    }

    setBenchmarks(bmData: BenchmarksDB.Data) {
        var bm = <any>this.app.$refs.benchmarks;
        bm.data = bmData;
        bm.show = true;
    }

    hideBenchmarks() {
        var bm = <any>this.app.$refs.benchmarks;
        //bm.show = false;
    }

    setEditorText(text: string) {
        (<any>this.app.$refs.editors).open(text);
    }

    async read(file: File) {
        return new TextDecoder().decode(await file.arrayBuffer());
    }

    message(msg: string) {
        var div = $('<div>').text(msg);
        this.notifications.append(div);
        setTimeout(() => div.remove(), 4000);
    }
}

type OpenOptions = {name?: string, silent?: boolean};
const DEFAULT_URL = '/trace.json';


class DragDropJson extends EventEmitter {

    constructor(container: JQuery) { 
        super();
        container.on('dragover', (ev) => {
            ev.preventDefault();
        });
        container.on('drop', (ev) => {
            this.drop(ev.originalEvent.dataTransfer);
            ev.preventDefault();
        });
    }

    async drop(dt: DataTransfer) {
        if (dt.files.length == 1) {
            this.emit('open', {file: dt.files[0]});
        }
        else this.emit('error', "Can only process one file at a time");
    }
}



export { MainDocument, OpenOptions, DragDropJson }
