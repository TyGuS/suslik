import { EventEmitter } from 'events';

import type { ProofTrace } from './proof-trace';
import './proof-interaction.css';


class ProofInteraction extends EventEmitter {
    baseURL: URL
    ws: WebSocket

    pt: ProofTrace
    view: Vue & View.Props

    constructor(pt: ProofTrace) {
        super();
        this.baseURL = new URL('http://localhost:8033');
        this.pt = pt;
        this.view = <any>pt.view;
        this.view.interaction = {focused: [], choices: undefined};
        this.view.$on('interaction:action', action => this.handleAction(action));
    }

    async start(spec?: Data.Spec) {
        this.ws = new WebSocket(`ws://${this.baseURL.host}${this.baseURL.pathname}`);
        this.ws.addEventListener('message', m => this.handleMessage(m.data));
        await new Promise((resolve, reject) => {
            this.ws.addEventListener('open', resolve);
            this.ws.addEventListener('error', reject)
        });
        if (spec) this.sendSpec(spec);
    }

    sendSpec(spec: Data.Spec) {
        this._send(spec, ProofInteraction.Data.Classes.SPEC);
    }

    sendChoose(choice: string) {
        this._send({choice}, ProofInteraction.Data.Classes.CHOOSE);
    }

    sendExpandRequest(nodeId: ProofTrace.Data.NodeId) {
        this._send({id: nodeId}, ProofInteraction.Data.Classes.EXPAND_REQUEST);
    }

    _send(json: any, $type?: string) {
        this.ws.send(JSON.stringify($type ? {$type, ...json} : json))
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

    handleAction(action: View.Action) {
        switch (action.type) {
        case 'select':
            this.view.interaction.choices = undefined; // clear choices
            this.sendChoose(action.goal.id);
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


import Data = ProofInteraction.Data;
import View = ProofInteraction.View;


namespace ProofInteraction {

    export namespace Data {

        export namespace Classes {
            const NS = "org.tygus.suslik.interaction.AsyncSynthesisRunner";

            export const SPEC           = `${NS}.SpecMessage`,
                         CHOOSE         = `${NS}.ChooseMessage`,
                         EXPAND_REQUEST = `${NS}.ExpandRequestMessage`;
        }

        export type Spec = {
            name?: string
            defs: string[]
            in: string
        }
    }

    export namespace View {

        export type Props = {
            interaction: ProofInteraction.View.State
            highlight: {[kind: string]: ProofTrace.Data.NodeId[]}
        };
    
        export type State = {
            focused: ProofTrace.Data.NodeId[]
            choices: ProofTrace.Data.GoalEntry[]
        };

        export type Action = {
            type: 'select'
            goal?: ProofTrace.Data.GoalEntry
        };

    }

}


export { ProofInteraction }