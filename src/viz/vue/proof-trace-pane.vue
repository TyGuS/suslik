<template>
    <div id="proof-trace-pane" class="ide-pane proof-trace-pane"
            :class="{'proof-trace-filter--only-success': options.proofOnly,
                     'proof-trace-filter--only-expanded': options.expandedOnly}"
            @mousedown="panStart" @mousemove="panMove" @mouseup="panEnd"
            @mousewheel="zoomPad" @scroll="onScroll">
        <app-toolbar :options="options" @action="toplevelAction($event)"/>
        <app-context-menu ref="contextMenu" @action="toplevelAction"/>
        <div ref="area">
            <template v-for="(t,id) in traces">
                <div class="proof-trace-pane-rendered" :key="id"
                        :class="{active: id === activeTrace}"
                        :style="{'--zoom': zoom/100}">
                    <proof-trace :root="t.root" :highlight="jointHigh"
                        @action="toplevelAction($event, id)"/>
                </div>
            </template>
        </div>
        <proof-interaction :choices="interaction && interaction.choices"
            :result="interaction && interaction.result"
            @action="$emit('interaction:action', $event)"/>
    </div>
</template>

<style>
.proof-trace-pane .proof-trace-pane-rendered:not(.active) {
    display: none;
}
</style>

<script>
import AppToolbar from './app-toolbar.vue';
import AppContextMenu from './app-context-menu';
import ProofTrace from './proof-trace.vue';
import ProofInteraction from './proof-interaction.vue';


export default {
    data: () => ({traces: {}, options: {}, zoom: 100, pscroll: {x: 0, y: 0},
                  activeTrace: undefined,
                  /* these are defunct for now... */
                  interaction: {}, highlight: {'special': [[]]}}),
    computed: {
        jointHigh() {
            return {'interact-focus': this.interaction?.focused, ...this.highlight};
        }
    },
    mounted() {
        requestAnimationFrame(() =>
            this._areaOffset = {x: this.$refs.area.offsetLeft, y: this.$refs.area.offsetTop});
    },
    methods: {
        toplevelAction(ev, id) {
            ev = {id, ...ev};
            switch (ev.type) {
            case 'menu': this.$refs.contextMenu.open(ev); break;
            }
            this.$emit('action', ev);
        },
        onScroll() {
            var sc = {x: this.$el.scrollLeft, y: this.$el.scrollTop};
            if (sc.x !== Math.round(this.pscroll.x) || sc.y !== Math.round(this.pscroll.y))
                this.pscroll = sc;
        },
        setZoom(newValue, around = {x:0, y:0}) {
            var u = this.zoom, v = this.zoom = newValue,
                sc = {x: (this.pscroll.x - around.x) * v / u + around.x,
                      y: (this.pscroll.y - around.y) * v / u + around.y};
            this.$el.scrollTop = Math.round(sc.y);
            this.$el.scrollLeft = Math.round(sc.x);
            this.pscroll = sc;
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
                var o = this._areaOffset,
                    xy = {x: o.x - (ev.pageX - this.$el.offsetLeft),
                          y: o.y - (ev.pageY - this.$el.offsetTop)};
                this.setZoom(this.zoom - ev.deltaY, xy);
                ev.stopPropagation();
                ev.preventDefault();
            }
        }
    },
    components: { AppToolbar, AppContextMenu, ProofTrace, ProofInteraction }
}
</script>
