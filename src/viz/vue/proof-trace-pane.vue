<template>
    <div id="proof-trace-pane" class="ide-pane proof-trace-pane"
            :class="{'proof-trace-filter--only-success': options.proofOnly,
                     'proof-trace-filter--only-expanded': options.expandedOnly}"
            @mousedown="panStart" @mousemove="panMove" @mouseup="panEnd"
            @mousewheel="zoomPad">
        <app-toolbar :options="options" @action="toplevelAction($event)"/>
        <app-context-menu ref="contextMenu" @action="toplevelAction"/>
        <template v-for="(t,id) in traces">
            <div class="proof-trace-pane-area" :style="{'--zoom': zoom/100}" :key="id">
                <proof-trace :root="t.root" :highlight="jointHigh"
                    @action="toplevelAction($event, id)"/>
            </div>
        </template>
        <!--
        <proof-interaction :choices="interaction && interaction.choices"
            @action="$emit('interaction:action', $event)"/> -->
    </div>
</template>

<script>
import AppToolbar from './app-toolbar.vue';
import AppContextMenu from './app-context-menu';
import ProofTrace from './proof-trace.vue';
import ProofInteraction from './proof-interaction.vue';


export default {
    data: () => ({traces: {}, options: {}, zoom: 100, 
         interaction: {}, highlight: {'special': [[]]}}),
    computed: {
        jointHigh() {
            return {'interact-focus': this.interaction?.focused, ...this.highlight};
        }
    },
    methods: {
        toplevelAction(ev, id) {
            ev = {id, ...ev};
            switch (ev.type) {
            case 'menu': this.$refs.contextMenu.open(ev); break;
            }
            this.$emit('action', ev);
        },
        setZoom(newValue) {
            var u = this.zoom, v = this.zoom = newValue;
            this.$el.scrollTop *= v / u;
            this.$el.scrollLeft *= v / u;
        },
        panStart(ev) {
            if (!ev.target.closest('.proof-trace-node')) {
                this._gesture = {x: ev.x, y: ev.y}
            }
        },
        panMove(ev) {
            if (this._gesture) {
                var u = this._gesture, v = this._gesture = {x: ev.x, y: ev.y};
                this.$el.scrollTop -= v.y - u.y;
                this.$el.scrollLeft -= v.x - u.x;
            }
        },
        panEnd(ev) {
            this._gesture = undefined;
        },
        zoomPad(ev) {
            if (ev.ctrlKey) {
                console.log(ev.offsetX, ev.offsetY);
                this.setZoom(this.zoom - ev.deltaY);
                ev.stopPropagation();
                ev.preventDefault();
            }
        }
    },
    components: { AppToolbar, AppContextMenu, ProofTrace, ProofInteraction }
}
</script>
