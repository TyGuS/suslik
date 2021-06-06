import { EventEmitter } from 'events';

import type { ProofTrace } from './proof-trace';
import './proof-interaction.css';


class ProofInteraction extends EventEmitter {
    baseURL: URL
    ws: WebSocket

    pt: ProofTrace
    view: Vue & ProofInteraction.ViewProps

    constructor(pt: ProofTrace) {
        super();
        this.baseURL = new URL('http://localhost:8033');
        this.pt = pt;
        this.view = <any>pt.view;
        this.view.interaction = {focused: [], choices: undefined};
        this.view.$on('interaction:action', action => this.handleAction(action));
    }

    start() {
        this.ws = new WebSocket(`ws://${this.baseURL.host}${this.baseURL.pathname}`);
        this.ws.addEventListener('message', m => this.handleMessage(m.data));
        return new Promise((resolve, reject) => {
            this.ws.addEventListener('open', resolve);
            this.ws.addEventListener('error', reject)
        });
    }
    
    continue(choice: string) {
        this.ws.send(choice);
    }

    handleMessage(data: string) {
        try {
            var msg = JSON.parse(data);
        }
        catch { console.error(data); return; }

        this.emit('message', msg);

        if (Array.isArray(msg)) {
            this.view.interaction.focused = this.getNodesForChoices(msg);
            this.view.interaction.choices = msg;
            this.emit('choose', msg);
        }
        else if (msg.procs) this.emit('done', msg);
        else if (msg.error) this.emit('error', {message: msg.error});
        else this.emit('trace', msg);
    }

    handleAction(action: ProofInteraction.View.Action) {
        switch (action.type) {
        case 'select':
            this.view.interaction.choices = undefined; // clear choices
            this.continue(action.goal.id);
            break;
        }
    }

    getNodesForChoices(choices: {from: ProofTrace.Data.GoalId[]}[]): ProofTrace.Data.NodeId[] {
        var ret: ProofTrace.Data.NodeId[] = [];
        for (let choice of choices) {
            for (let goalId of choice.from) {
                let node = this.pt.nodeIndex.byGoalId.get(goalId);
                if (node) ret.push(node.id);
            }
        }
        return ret;
    }

    fetch(urlPath: string, options?: {}) {
        return fetch(this._url(urlPath).href, options);
    }

    _url(urlPath: string) { return new URL(urlPath, this.baseURL); }
}


namespace ProofInteraction {

    export type ViewProps = {
        interaction: ProofInteraction.View.State
        highlight: {[kind: string]: ProofTrace.Data.NodeId[]}
    }

    export namespace View {

        export type State = {
            focused: ProofTrace.Data.NodeId[]
            choices: ProofTrace.Data.GoalEntry[]
        }

        export type Action = {
            type: 'select'
            goal?: ProofTrace.Data.GoalEntry
        }

    }

}


export { ProofInteraction }