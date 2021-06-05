import { EventEmitter } from 'events';
import $ from 'jquery';

import { ProofTrace } from './proof-trace';



class MainDocument extends EventEmitter {

    pt: ProofTrace
    pane: JQuery
    notifications: JQuery

    storage: {'suslik:doc:lastUrl'?: string} = <any>localStorage;

    constructor(pane: JQuery, notifications: JQuery) {
        super();
        this.pane = pane;
        this.notifications = notifications;
    }

    new() {
        return this.set(new ProofTrace(ProofTrace.Data.empty()));
    }

    async open(content: string | File, opts: OpenOptions = {}): Promise<ProofTrace> {
        if (content instanceof File) {
            return this.open(await this.read(content), {name: content.name, ...opts});
        }
        else {
            try {
                var data = ProofTrace.Data.parse(content);
                return this.set(new ProofTrace(data));
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

    set(pt: ProofTrace) {
        this.pt = pt;
        this.pane.replaceWith(this.pane = $(pt.view.$el as HTMLElement));
        this.emit('open', pt);
        return pt;
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
