import type Vue from 'vue';


class VueEventHook {
    event: string
    instance: Vue
    eh: Function

    constructor(event: string) { this.event = event; }

    attach(instance: Vue, eh: Function) {
        this.detach();
        this.instance = instance;
        this.eh = eh;
        instance.$on(this.event, eh);
    }

    detach() {
        if (this.instance) {
            this.instance.$off(this.event, this.eh);
            this.instance = this.eh = undefined;
        }
    }
}


export { VueEventHook }
