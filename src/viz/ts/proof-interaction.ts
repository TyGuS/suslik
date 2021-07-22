import { EventEmitter } from 'events';

import { VueEventHook } from './infra/event-hooks';
import type { ProofTrace } from './proof-trace';
import type { BenchmarksDB } from './benchmarks';

import './proof-interaction.css';



class ProofInteraction extends EventEmitter {
    wsURL: string
    ws: WebSocket

    pt: ProofTrace
    view: View.State

    _actionHook = new VueEventHook('interaction:action')

    defaultMode = ProofInteraction.Data.ProofMode.INTERACTIVE

    constructor(pt: ProofTrace, pane: Vue) {
        super();
        this.wsURL = this._wsURL();
        this.pt = pt;
        this.view = (<any>pane).interaction = {focused: [], choices: undefined, result: undefined} //<any>pt.view;
        //this.view.interaction = {focused: [], choices: undefined, result: undefined};
        this._actionHook.attach(pane, action => this.handleAction(action));
    }

    destroy() {
        this._actionHook.detach();
        this.ws?.close();
    }

    async start(spec?: Data.Spec, mode?: Data.ProofMode) {
        this.ws = new WebSocket(this.wsURL);
        this.ws.addEventListener('message', m => this.handleMessage(m.data));
        await new Promise((resolve, reject) => {
            this.ws.addEventListener('open', resolve);
            this.ws.addEventListener('error', reject)
        });
        this.ws.addEventListener('error', err => this.emit('error', err));
        if (spec) this.sendSpec(spec, mode);
    }

    sendSpec(spec: Data.Spec, mode: Data.ProofMode = this.defaultMode) {
        this._send({mode, ...spec}, ProofInteraction.Data.Classes.SPEC);
    }

    sendChoose(choice: string) {
        this._send({choice}, ProofInteraction.Data.Classes.CHOOSE);
    }

    sendExpandRequest(nodeId: ProofTrace.Data.NodeId) {
        this._send({id: nodeId}, ProofInteraction.Data.Classes.EXPAND_REQUEST);
    }

    _send(json: any, $type?: string) {
        if (this.ws.readyState !== WebSocket.OPEN) {
            this.emit('error', {message: 'disconnected from server'});
            return;
        }
        this.ws.send(JSON.stringify($type ? {$type, ...json} : json))
    }
    
    handleMessage(data: string) {
        try {
            var msg = JSON.parse(data);
        }
        catch { console.error(data); return; }

        this.emit('message', msg);

        if (Array.isArray(msg)) {
            this.view.focused = this.getNodesForChoices(msg);
            this.view.choices = msg;
            this.emit('choose', msg);
        }
        else if (msg.procs) {
            this.view.result = msg;
            this.emit('done', msg);
        }
        else if (msg.error) this.emit('error', {message: msg.error});
        else this.emit('trace', msg);
    }

    handleAction(action: View.Action) {
        switch (action.type) {
        case 'select':
            this.view.choices = undefined; // clear choices
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

    _wsURL() {
        switch (window.location.protocol) {
            case 'https:': return `wss://${location.host}${location.pathname}`;
            case 'http:': return `ws://${location.host}${location.pathname}`;
            default: return 'ws://localhost:8033'; // dev mode
        }
    }
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

        export type Spec = BenchmarksDB.Data.Spec;

        export enum ProofMode {
            AUTOMATIC = "automatic",
            INTERACTIVE = "interactive"
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
            result: {procs: {pp: string}[]}
        };

        export type Action = {
            type: 'select'
            goal?: ProofTrace.Data.GoalEntry
        };

    }

}



export { ProofInteraction }