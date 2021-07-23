<template>
    <div class="proof-trace-toolbar">
        <div class="toolbox">
            <template v-if="options.auto">
                <button @click="action('start')">
                    <svg viewBox="0 0 512 844" width=".5em" xmlns="http://www.w3.org/2000/svg"> <path d="M0 192l512 320L0 832V192z"/> </svg>
                </button>
                <button @click="action('stop')">
                    <svg viewBox="0 0 512 844" width=".5em" xmlns="http://www.w3.org/2000/svg"> <path d="M512 768H0V256h512V768z" /> </svg>
                </button>
            </template>
            <template v-else>
                <button @click="action('restart')">↻</button>
            </template>
        </div>
        <form>
            <!--
            Show:
            <input type="checkbox" name="proof-only" id="proof-only" v-model="options.proofOnly">
            <label for="proof-only">Proof only</label>
            <input type="checkbox" name="expanded-only" id="expanded-only" v-model="options.expandedOnly">
            <label for="expended-only">Expanded only</label>
            -->
            <span style="margin-left: 2em">Traditional</span>
            <slider-switch v-model="options.simple"></slider-switch>
            <span>Simplified</span>

            <span style="margin-left: 2em">Manual</span>
            <slider-switch v-model="options.auto"></slider-switch>
            <span>Auto</span>
        </form>
    </div>
</template>

<style>
div.proof-trace-toolbar {
    box-sizing: border-box;
    white-space: nowrap;
    font-family: 'Trebuchet MS', 'Lucida Sans Unicode', 'Lucida Grande', 'Lucida Sans', Arial, sans-serif;
}

div.proof-trace-toolbar form {
    padding: 1em 1em .75em 1em;
}
div.proof-trace-toolbar form span {
    font-size: 85%;
    position: relative;
    top: -.12em;
}

div.proof-trace-toolbar .toolbox {
    float: right;
    padding: .5em .5em 0 0;
}
div.proof-trace-toolbar .toolbox button {
    font-size: 150%;
}
</style>

<script>
import SliderSwitch from './widgets/slider-switch.vue';


export default {
    props: {options: {default: () => ({})}},
    methods: {
        action(type) {
            this.$emit('action', {type});
        }
    },
    components: { SliderSwitch }
}
</script>
