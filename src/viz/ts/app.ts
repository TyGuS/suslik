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
    view: Vue & SuSLikApp.Props
    notifications: JQuery

    doc: MainDocument
    docsById = new Map<string, MainDocument>()

    panes: {proofTrace: any, benchmarks: any, editors: any}

    constructor(notifications: JQuery) {
        super();
        this.notifications = notifications;
        this.view = <any>new Vue(app).$mount();
        this.panes = <any>this.view.$refs;  /* I like the sound they make when they break */

        this.panes.proofTrace.$on('action', ev => {
            this.emit('proofTrace:action', ev);
        });
        this.panes.benchmarks.$on('action', ev => {
            this.emit('benchmarks:action', ev);
        });
    }

    get $el() { return this.view.$el; }

    get options() {
        return this.panes.proofTrace.options;
    }

    add(doc: MainDocument) {
        this.docsById.get(doc.id)?.close();
        this.docsById.set(doc.id, doc);
        this.doc = doc;
        doc.on('error', err => this.message(err.message));
        this.switchTo(doc.id);
    }

    has(docId: string) {
        return this.docsById.has(docId);
    }

    switchTo(docId: string) {
        var doc = this.docsById.get(docId);
        if (doc) {
            this.panes.proofTrace.activeTrace = docId;
            this.doc = doc;
        }
        else console.warn(`no such document: '${docId}'`)
    }

    clear() {
        for (let doc of this.docsById.values()) doc.close();
        this.docsById.clear();
        this.doc = undefined;
    }

    setBenchmarks(bmData: BenchmarksDB.Data) {
        var bm = this.panes.benchmarks;
        bm.data = bmData;
    }

    setActiveBenchmark(activeBenchmark: SuSLikApp.BenchmarkEntry) {
        this.view.activeBenchmark = activeBenchmark;
    }

    hideBenchmarks() {
        /** @todo */
    }

    setEditorText(text: string) {
        this.panes.editors.open(text);
    }

    getEditorText() {
        return this.panes.editors.current();
    }

    message(msg: string) {
        var div = $('<div>').text(msg);
        this.notifications.append(div);
        setTimeout(() => div.remove(), 4000);
    }
}


namespace SuSLikApp {
    export type BenchmarkEntry = {
        path: {dir: string, fn: string}
    };

    export type Props = {
        activeBenchmark: BenchmarkEntry
    }
}


class MainDocument extends EventEmitter {
    id: string
    pane: Vue & ProofTrace.View.PaneProps & ProofInteraction.View.PaneProps
    options: DocumentOptions

    pt: ProofTrace
    pi: ProofInteraction

    props: any

    storage: {'suslik:doc:lastUrl'?: string} = <any>localStorage;

    constructor(id: string, pane: Vue & ProofTrace.View.PaneProps & ProofInteraction.View.PaneProps,
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
        pi.on('error', err =>
            this.emit('error', {message: `oops: ${err.message}`}));

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
