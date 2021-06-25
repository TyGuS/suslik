import { EventEmitter } from 'events';
import _ from 'lodash';
import $ from 'jquery';
import Vue from 'vue';

// @ts-ignore
import app from '../vue/app.vue';
import { BenchmarksDB } from './benchmarks';
import { ProofTrace } from './proof-trace';
import { ProofInteraction } from './proof-interaction';

import './ide.css';



class SuSLikApp extends EventEmitter {
    app: Vue
    notifications: JQuery

    doc: MainDocument

    constructor(notifications: JQuery) {
        super();
        this.notifications = notifications;
        this.app = new Vue(app).$mount();

        (<Vue>this.app.$refs.proofTrace).$on('action', ev => {
            this.emit('proofTrace:action', ev);
        });
        (<Vue>this.app.$refs.benchmarks).$on('action', ev => {
            this.emit('benchmarks:action', ev);
        });
    }

    get $el() { return this.app.$el; }

    get options() {
        return (<any>this.app.$refs.proofTrace).options;
    }

    add(doc: MainDocument) {
        this.doc?.close();
        this.doc = doc;
        doc.on('error', err => this.message(err.message));
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

    getEditorText() {
        return (<any>this.app.$refs.editors).current();
    }

    message(msg: string) {
        var div = $('<div>').text(msg);
        this.notifications.append(div);
        setTimeout(() => div.remove(), 4000);
    }
}


class MainDocument extends EventEmitter {
    id: string
    pane: Vue & ProofTrace.View.PaneProps
    options: DocumentOptions

    pt: ProofTrace
    pi: ProofInteraction

    props: any

    storage: {'suslik:doc:lastUrl'?: string} = <any>localStorage;

    constructor(id: string, pane: Vue & ProofTrace.View.PaneProps,
                options: DocumentOptions = {}) {
        super();
        this.id = id;
        this.pane = pane;
        this.options = options;
    }

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
                    this.emit('error', {message: `Cannot open '${opts.name}': ${msg}`});
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
        return this.openUrl(this.storage['suslik:doc:lastUrl'] || MainDocument.DEFAULT_URL, opts);
    }

    setProofTrace(ptData: ProofTrace.Data) {
        this.pt?.destroy();
        this.pi?.destroy();

        var pt = new ProofTrace(this.id, ptData, this.pane),
            pi = new ProofInteraction(pt, this.pane);
        this.pt = pt;
        this.pi = pi;
        pt.on('expand', (nodeView: ProofTrace.View.Node) => {
            if (nodeView.value.tag == ProofTrace.Data.NodeType.OrNode &&
                nodeView.children.length == 0) {
                /* send request to server */
                if (this.pi) this.pi.sendExpandRequest(nodeView.value.id);
            }
        });

        pi.on('trace', throttleCollate((values: [any][]) => {
            this.pt.append(ProofTrace.Data.fromEntries(values.map(x => x[0])),
                           {expand: this.options.expandImmediately});
        }, this.options.throttle));
        
        this.emit('open', pt);
        return pt;
    }

    async read(file: File) {
        return new TextDecoder().decode(await file.arrayBuffer());
    }

    close() {
        this.pt?.destroy();
        this.pi?.destroy();
    }
}

namespace MainDocument {
    export type Options = {
        throttle?: number           /* min delay between trace updates */
        expandImmediately?: true    /* whether to expand nodes as soon as they are received */
    };
    export type OpenOptions = {name?: string, silent?: boolean};
    export const DEFAULT_URL = '/trace.json';
}

import DocumentOptions = MainDocument.Options;
import OpenOptions = MainDocument.OpenOptions;


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


/**
 * Service routine; throttle call then invoke with accumulated
 * lists of args.
 */
function throttleCollate<T extends any[]>(func: (c: T[]) => void, wait?: number) {
    var queue = [],
        tflush = _.throttle(() => { func(queue); queue = []; }, wait);
    return (...args: any[]) => { queue.push(args); tflush(); };
}



export { SuSLikApp, MainDocument, OpenOptions, DragDropJson }
