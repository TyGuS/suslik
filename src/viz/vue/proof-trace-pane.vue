<template>
    <div id="proof-trace-pane" 
        :class="{'proof-trace-filter--only-success': options.proofOnly,
                    'proof-trace-filter--only-expanded': options.expandedOnly}">
        <app-toolbar :options="options"/>
        <app-context-menu ref="contextMenu" @action="toplevelAction"/>
        <div class="proof-trace-pane-area" :style="{'--zoom': zoom}">
            <proof-trace :root="root" :highlight="jointHigh"
                @action="toplevelAction"/>
        </div>
        <proof-interaction :choices="interaction && interaction.choices"
            @action="$emit('interaction:action', $event)"/>
    </div>
</template>

<script>
import AppToolbar from './app-toolbar.vue';
import AppContextMenu from './app-context-menu';
import ProofTrace from './proof-trace.vue';
import ProofInteraction from './proof-interaction.vue';


export default {
    props: ['root', 'interaction'],
    data: () => ({options: {}, zoom: 1, highlight: {'special': [[]]}}),
    computed: {
        jointHigh() {
            return {'interact-focus': this.interaction?.focused, ...this.highlight};
        }
    },
    methods: {
        toplevelAction(ev) {
            switch (ev.type) {
            case 'menu': this.$refs.contextMenu.open(ev); break;
            }
            this.$emit('action', ev);
        }
    },
    components: { AppToolbar, AppContextMenu, ProofTrace, ProofInteraction }
}
</script>
